/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Heather Macbeth
-/

import Mathlib

namespace MvPolynomial

open MvPolynomial

noncomputable def leadingHomogeneousComponent {R σ : Type*} [CommSemiring R]
  (f : MvPolynomial σ R) := f.homogeneousComponent f.totalDegree

theorem leadingHomogeneousComponent_apply {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) :
  f.leadingHomogeneousComponent = f.homogeneousComponent f.totalDegree := rfl

theorem leadingHomogeneousComponent_isHomogeneous {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) : f.leadingHomogeneousComponent.IsHomogeneous (f.totalDegree) := by
  rw [leadingHomogeneousComponent_apply]
  exact homogeneousComponent_isHomogeneous _ _

theorem leadingHomogeneousComponent_totalDegree {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) :
    f.leadingHomogeneousComponent.totalDegree = f.totalDegree := by
  unfold leadingHomogeneousComponent
  by_cases! hf : f = 0
  · simp [hf]
  · have h := homogeneousComponent_isHomogeneous (f.totalDegree) f
    apply le_antisymm h.totalDegree_le
    obtain ⟨m, hm1, hm2⟩ : ∃ m ∈ f.support, m.sum (fun x e ↦ e) = f.totalDegree := by
      rw [totalDegree]
      conv => right; intro m; right; rw [eq_comm]
      exact Finset.exists_mem_eq_sup _ (support_nonempty.mpr hf) _
    nth_rw 1 [← hm2]
    apply le_totalDegree
    rw [mem_support_iff, coeff_homogeneousComponent]
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp]
    refine ⟨?_ , mem_support_iff.mp hm1⟩
    rwa [Finsupp.sum, ← Finsupp.degree_apply] at hm2

theorem mem_support_homogeneousComponent {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (n : ℕ) (s : σ →₀ ℕ) :
    s ∈ (f.homogeneousComponent n).support ↔ s ∈ f.support ∧ s.degree = n := by
  classical
  simp only [homogeneousComponent_apply, mem_support_iff, coeff_sum, coeff_monomial,
    eq_comm, Finset.sum_ite_eq, Finset.mem_filter, ite_ne_right_iff]
  tauto

theorem homogeneousComponent_support_subset {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (n : ℕ) : (f.homogeneousComponent n).support ⊆ f.support := by
  intro s hs
  rw [mem_support_homogeneousComponent] at hs
  tauto

theorem leadingHomogeneousComponent_eq_zero {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) : f.leadingHomogeneousComponent = 0 ↔ f = 0 := by
  unfold leadingHomogeneousComponent
  constructor
  · intro hf
    by_contra! h
    obtain ⟨m, hm⟩ : ∃ m ∈ f.support, m.degree = f.totalDegree := by
      rw [totalDegree]
      conv => right; intro m; right; rw [eq_comm]
      apply Finset.exists_mem_eq_sup
      rwa [support_nonempty]
    rw [← mem_support_homogeneousComponent] at hm
    simp [hf] at hm
  · intro hf
    simp [hf]

theorem homogeneousComponent_coeff {R σ : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (n : ℕ) (s : σ →₀ ℕ) :
    (f.homogeneousComponent n).coeff s = if s.degree = n then f.coeff s else 0 := by
  classical
  conv => left; simp only [homogeneousComponent_apply, coeff_sum, coeff_monomial, eq_comm (b := s),
    Finset.sum_ite_eq, Finset.mem_filter, mem_support_iff]
  by_cases! h : f.coeff s = 0 <;> simp [h]

theorem homogeneousComponent_monomial {R σ : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) (c : R) (n : ℕ) :
    (monomial m c).homogeneousComponent n = if m.degree = n then (monomial m c) else 0 := by
  classical
  by_cases! hc : c = 0
  · simp [hc]
  conv =>
    left; simp only [homogeneousComponent_apply, support_monomial, hc, if_false, Finset.sum_filter,
      Finset.sum_singleton, coeff_monomial, if_true]

theorem homogeneousComponent_mul_of_totalDegree_le {R σ : Type*} [CommSemiring R]
    {f g : MvPolynomial σ R} {n m : ℕ} (hn : f.totalDegree ≤ n) (hm : g.totalDegree ≤ m) :
    (f * g).homogeneousComponent (n + m) = f.homogeneousComponent n * g.homogeneousComponent m := by
  classical
  by_cases hnm : n = 0 ∧ m = 0
  · simp only [hnm, add_zero, homogeneousComponent_zero, ← C_mul]
    simp [coeff_mul, Finset.antidiagonal_zero]
  simp only [not_and_or, ← Nat.pos_iff_ne_zero] at hnm
  simp only [mul_def, Finsupp.sum, map_sum]
  rw [← Finset.sum_subset (s₁ := (f.homogeneousComponent n).support)]
  rotate_left
  · exact homogeneousComponent_support_subset f n
  · intro x hx1 hx2
    by_contra!
    obtain ⟨y, hy1, hy2⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
    contrapose! hy2
    by_cases! hc : f.coeff x * g.coeff y = 0
    <;> simp only [coeff] at hc
    · simp [hc]
    · apply homogeneousComponent_eq_zero
      rw [totalDegree_monomial _ hc, Finsupp.sum_add_index]
      any_goals simp
      have : x.sum (fun i e ↦ e) < n := by
        rw [mem_support_homogeneousComponent, not_and] at hx2
        specialize hx2 hx1
        apply le_trans (le_totalDegree hx1) at hn
        rw [Finsupp.degree_apply] at hx2
        rw [Finsupp.sum] at hn ⊢
        exact lt_of_le_of_ne hn hx2
      have : y.sum (fun i e ↦ e) ≤ m := le_trans (le_totalDegree hy1) hm
      linarith
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_subset (s₁ := (g.homogeneousComponent m).support)]
  rotate_left
  · exact homogeneousComponent_support_subset g m
  · intro y hy1 hy2
    by_cases! hc : f.coeff x * g.coeff y = 0
    <;> simp only [coeff] at hc
    · simp [hc]
    · apply homogeneousComponent_eq_zero
      rw [totalDegree_monomial _ hc, Finsupp.sum_add_index]
      any_goals simp
      have : x.sum (fun i e ↦ e) ≤ n := by
        obtain ⟨hx1, -⟩ := mem_support_homogeneousComponent f n x |>.mp hx
        exact le_trans (le_totalDegree hx1) hn
      have : y.sum (fun i e ↦ e) < m := by
        rw [mem_support_homogeneousComponent, not_and] at hy2
        specialize hy2 hy1
        apply le_trans (le_totalDegree hy1) at hm
        rw [Finsupp.degree_apply] at hy2
        rw [Finsupp.sum] at hm ⊢
        exact lt_of_le_of_ne hm hy2
      linarith
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨hx1, hx2⟩ := mem_support_homogeneousComponent f n x |>.mp hx
  obtain ⟨hy1, hy2⟩ := mem_support_homogeneousComponent g m y |>.mp hy
  have : (x + y).degree = n + m := by rw [map_add, hx2, hy2]
  simp only [homogeneousComponent_monomial, this, if_true]
  simp only [← monomial_mul]
  congr 2
  · have := homogeneousComponent_coeff f n x
    simpa [hx2, coeff, eq_comm] using this
  · have := homogeneousComponent_coeff g m y
    simpa [hy2, coeff, eq_comm] using this

theorem totalDegree_mul_eq {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]
    {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).totalDegree = f.totalDegree + g.totalDegree:= by
  apply le_antisymm (totalDegree_mul _ _)
  by_contra! hcontra
  have h := homogeneousComponent_mul_of_totalDegree_le
    (le_refl f.totalDegree) (le_refl g.totalDegree)
  simp only [homogeneousComponent_eq_zero _ _ hcontra, ← leadingHomogeneousComponent_apply] at h
  simp [leadingHomogeneousComponent_eq_zero, hf, hg] at h

theorem homogeneousComponent_pow_of_totalDegree_le {R σ : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {n : ℕ} (hn : f.totalDegree ≤ n) (k : ℕ) :
    (f ^ k).homogeneousComponent (k * n) = f.homogeneousComponent n ^ k := by
  induction k
  case zero => simp
  case succ k hk =>
    by_cases! hk0 : k = 0
    · simp [hk0]
    simp only [add_mul, one_mul, pow_succ, ← hk]
    apply homogeneousComponent_mul_of_totalDegree_le _ hn
    apply le_trans (totalDegree_pow _ _)
    rwa [Nat.mul_le_mul_left_iff (Nat.pos_iff_ne_zero.mpr hk0)]

theorem leadingHomogeneousComponent_mul {R σ : Type*} [CommSemiring R] [NoZeroDivisors R]
    (f g : MvPolynomial σ R) : (f * g).leadingHomogeneousComponent =
    f.leadingHomogeneousComponent * g.leadingHomogeneousComponent := by
  simp only [leadingHomogeneousComponent_apply]
  by_cases! h0 : f = 0 ∨ g = 0
  · rcases h0 with rfl | rfl <;> simp
  simp [← homogeneousComponent_mul_of_totalDegree_le, totalDegree_mul_eq, h0]

-- TODO: instIsReduced uses CommRing but CommSemiring should be enough?
theorem totalDegree_pow_eq {R σ : Type*} [CommRing R] [IsReduced R]
    (f : MvPolynomial σ R) (n : ℕ) : (f ^ n).totalDegree = n * f.totalDegree := by
  by_cases! hn : n = 0
  · simp [hn]
  by_cases! hf : f = 0
  · simp [hn, hf]
  apply le_antisymm (totalDegree_pow _ _)
  by_contra! hcontra
  have h := homogeneousComponent_pow_of_totalDegree_le (le_refl f.totalDegree) n
  simp only [homogeneousComponent_eq_zero _ _ hcontra, ← leadingHomogeneousComponent_apply] at h
  simp [eq_comm, pow_eq_zero_iff hn, leadingHomogeneousComponent_eq_zero, hf] at h

theorem leadingHomogeneousComponent_pow {R σ : Type*} [CommRing R]
    [IsReduced R] (f : MvPolynomial σ R) (n : ℕ) :
    (f ^ n).leadingHomogeneousComponent = f.leadingHomogeneousComponent ^ n := by
  simp only [leadingHomogeneousComponent_apply]
  by_cases hn : n = 0
  · simp [hn]
  by_cases! hf : f = 0
  · simp [hf, hn]
  simp [← homogeneousComponent_pow_of_totalDegree_le, totalDegree_pow_eq]

theorem aeval_mul {R σ S₁: Type*} [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] (f : σ → S₁)
    (φ₁ φ₂ : MvPolynomial σ R) : (φ₁ * φ₂).aeval f = φ₁.aeval f * φ₂.aeval f := by simp

theorem aeval_pow {R σ S₁: Type*} [CommSemiring R] [CommSemiring S₁] [Algebra R S₁] (f : σ → S₁)
    (φ : MvPolynomial σ R) (n : ℕ) : (φ ^ n).aeval f = φ.aeval f ^ n := by simp

end MvPolynomial

open MvPolynomial

noncomputable def y_zero {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) :
    Polynomial R := f.aeval (fun₀ | (0 : Fin 2) => Polynomial.X | 1 => Polynomial.C c)

lemma y_zero_apply {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) :
    y_zero f c = f.aeval (fun₀ | (0 : Fin 2) => Polynomial.X | 1 => Polynomial.C c) := rfl

lemma y_zero_sum {R ι : Type*} [CommSemiring R] (f : ι → MvPolynomial (Fin 2) R)
    (s : Finset ι) (c : R) : y_zero (∑ i ∈ s, f i) c = ∑ i ∈ s, y_zero (f i) c := by
  simp [y_zero_apply]

lemma y_zero_pow {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) (k : ℕ) :
    y_zero (f ^ k) c = y_zero f c ^ k := by simp [y_zero_apply, aeval]

lemma y_zero_monomial_zero {R : Type*} [CommSemiring R] (m : Fin 2 →₀ ℕ) (c : R) :
    y_zero (monomial m c) 0 = if m 1 = 0 then Polynomial.monomial (m 0) c else 0 := by
  by_cases! hm : m 1 = 0
  <;> simp [y_zero_apply, aeval_monomial, hm, Polynomial.C_mul_X_pow_eq_monomial]

lemma y_zero_eq_sum_y_zero_monomial {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R)
    (c : R) : y_zero f c = ∑ m ∈ f.support, y_zero (monomial m (f.coeff m)) c := by
  set g := fun (m : Fin 2 →₀ ℕ) ↦ monomial m (f.coeff m) with hg
  have := f.as_sum
  simp only [← hg] at this
  rw [this, y_zero_sum, ← this]

noncomputable def x_zero {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) :
    Polynomial R := f.aeval (fun₀ | (0 : Fin 2) => Polynomial.C c | 1 => Polynomial.X)

lemma x_zero_apply {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) :
    x_zero f c = f.aeval (fun₀ | (0 : Fin 2) => Polynomial.C c | 1 => Polynomial.X) := rfl

lemma x_zero_sum {R ι : Type*} [CommSemiring R] (f : ι → MvPolynomial (Fin 2) R)
    (s : Finset ι) (c : R) : x_zero (∑ i ∈ s, f i) c = ∑ i ∈ s, x_zero (f i) c := by
  simp [x_zero_apply]

lemma x_zero_pow {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R) (c : R) (k : ℕ) :
    x_zero (f ^ k) c = x_zero f c ^ k := by simp [x_zero_apply, aeval]

lemma x_zero_monomial_zero {R : Type*} [CommSemiring R] (m : Fin 2 →₀ ℕ) (c : R) :
    x_zero (monomial m c) 0 = if m 0 = 0 then Polynomial.monomial (m 1) c else 0 := by
  by_cases! hm : m 0 = 0
  <;> simp [x_zero_apply, aeval_monomial, hm, Polynomial.C_mul_X_pow_eq_monomial]

lemma x_zero_eq_sum_x_zero_monomial {R : Type*} [CommSemiring R] (f : MvPolynomial (Fin 2) R)
    (c : R) : x_zero f c = ∑ m ∈ f.support, x_zero (monomial m (f.coeff m)) c := by
  set g := fun (m : Fin 2 →₀ ℕ) ↦ monomial m (f.coeff m) with hg
  have := f.as_sum
  simp only [← hg] at this
  rw [this, x_zero_sum, ← this]

namespace Polynomial

theorem coeff_sum' {ι R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by simp

theorem coeff_ite {R : Type*} [CommSemiring R] (P : Prop) [Decidable P] (f g : Polynomial R)
    (n : ℕ) : (if P then f else g).coeff n = if P then f.coeff n else g.coeff n := by
  rw [apply_ite (Polynomial.coeff (R := R) · n) P]

end Polynomial

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

local notation "⟪" n ", " m "⟫" => (Finsupp.single 0 n + Finsupp.single 1 m)

noncomputable def motzkin : MvPolynomial (Fin 2) K :=
  (monomial ⟪4, 2⟫ 1) + (monomial ⟪2, 4⟫ 1) - (monomial ⟪2, 2⟫ 3) + (monomial 0 1)

lemma motzkin_nonneg : ∀ r, (0 : K) ≤ motzkin.eval r := by
  have (x y : K) : 0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
    by_cases hx : x = 0
    · simp [hx]
    have h : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
    refine nonneg_of_mul_nonneg_left ?_ h
    have H : 0 ≤ (x ^ 3 * y + x * y ^ 3 - 2 * x * y) ^ 2 * (1 + x ^ 2 + y ^ 2)
      + (x ^ 2 - y ^ 2) ^ 2 := by positivity
    linear_combination H
  simp [motzkin, eval, ← mul_assoc, this]

lemma support_motzkin : motzkin (K := K).support = {⟪2, 4⟫, ⟪4, 2⟫, ⟪2, 2⟫, 0} := by
  ext x
  rw [motzkin]
  constructor
  · intro h
    rw [mem_support_iff] at h
    contrapose! h
    simp only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton, not_or] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [coeff_add, coeff_sub, coeff_monomial]
    simp [eq_comm, h1, h2, h3, h4,]
  · intro h
    simp only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    all_goals
    rw [mem_support_iff]
    simp only [coeff_add, coeff_sub, coeff_monomial]
    simp [Finsupp.ext_iff]

lemma totalDegree_motzkin : motzkin (K := K).totalDegree = 6 := by
  rw [totalDegree, support_motzkin]
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm
    simp only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl
    <;> simp [Finsupp.sum, Finset.sum_subset (Finset.subset_univ ..)]
  · simp [Finsupp.sum, Finset.sum_subset (Finset.subset_univ ..)]

open Polynomial in
lemma natDegree_sos {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → Polynomial K) :
    (∑ i ∈ s, f i ^ 2).natDegree = s.sup fun i ↦ (f i ^ 2).natDegree := by
  by_cases! h0 : s.sup (fun i ↦ (f i ^ 2).natDegree) = 0
  · exact le_antisymm (natDegree_sum_le _ _) (h0 ▸ (Nat.zero_le _))
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le _ _) ?_
  obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup s hs (fun i ↦ (f i ^ 2).natDegree)
  have hi3 := hi2
  simp only [natDegree_pow, ← Finset.mul_sup₀, mul_eq_mul_left_iff, or_false, two_ne_zero] at hi3
  have : ∀ x ∈ s, (f x ^ 2).coeff (f i ^ 2).natDegree = (f x).coeff (f i).natDegree ^ 2 := by
    intro x hx
    rw [natDegree_pow, coeff_pow_of_natDegree_le]
    exact hi3 ▸ Finset.le_sup (f := fun i ↦ (f i).natDegree) hx
  rw [hi2, finset_sum_coeff, Finset.sum_congr rfl this]
  intro h
  rw [Finset.sum_eq_zero_iff_of_nonneg (by simp [sq_nonneg])] at h
  specialize h i hi1
  rw [sq_eq_zero_iff, coeff_natDegree, leadingCoeff_eq_zero] at h
  simp only [h, natDegree_pow 0, natDegree_zero, mul_zero] at hi2
  exact h0 hi2

-- TODO: use Finsupp.degree instead of Finsupp.sum fun x e ↦ e?
lemma motzkin_ne_sos {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin 2) K) :
    motzkin ≠ ∑ i ∈ s, g i ^ 2 := by
  by_contra! motzkin_sos

  have s_nonempty : s.Nonempty := by
    by_contra! rfl
    simp only [Finset.sum_empty] at motzkin_sos
    rw [eq_zero_iff] at motzkin_sos
    specialize motzkin_sos 0
    simp [motzkin] at motzkin_sos

  have totalDegree_le_three : ∀ i ∈ s, ∀ m ∈ (g i).support, m 0 + m 1 ≤ 3 := by
    set d := s.sup fun i ↦ (g i).totalDegree with hd
    suffices d ≤ 3 by
      rw [hd, Finset.sup_le_iff] at this
      intro i hi m hm
      specialize this i hi
      rw [totalDegree] at this
      conv at this =>
        left; right;
        simp [Finsupp.sum, Finset.sum_subset (Finset.subset_univ _)]
      apply le_trans _ this
      exact Finset.le_sup (f := fun m ↦  m 0 + m 1) hm
    by_contra! hcontra
    replace h1 := congr(($motzkin_sos).homogeneousComponent (2 * d))
    rw [homogeneousComponent_eq_zero] at h1; swap
    · simp [totalDegree_motzkin]
      linarith
    rw [map_sum] at h1
    have h2 : ∀ i ∈ s, homogeneousComponent (2 * d) (g i ^ 2) =
        homogeneousComponent d (g i) ^ 2 := by
      intro i hi
      unfold d
      rw [homogeneousComponent_pow_of_totalDegree_le]
      exact Finset.le_sup (f := fun i ↦ (g i).totalDegree) hi
    rw [Finset.sum_congr rfl h2] at h1
    have h3 : ∀ x ∈ s, ∀ r, (homogeneousComponent d (g x)).eval r = 0 := by
      intro x hx r
      replace h1 := congr(($h1).eval r)
      simp only [map_zero, map_sum, map_pow] at h1
      rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg (by simp [sq_nonneg])] at h1
      simpa using h1 x hx
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup s s_nonempty (fun i ↦ (g i).totalDegree)
    rw [← hd] at hi2
    specialize h3 i hi1
    simp only [hi2, ← leadingHomogeneousComponent_apply] at h3
    have := leadingHomogeneousComponent_isHomogeneous (g i)
    apply this.eq_zero_of_forall_eval_eq_zero at h3
    rw [leadingHomogeneousComponent_eq_zero] at h3
    simp [hi2, h3] at hcontra

  have x_iff_y : ∀ i ∈ s, ∀ m ∈ (g i).support, 0 < m 0 ↔ 0 < m 1 := by
    by_contra! ⟨i, hi1, ⟨m, hm1, (⟨hm2, hm3⟩ | ⟨hm2, hm3⟩)⟩⟩
    · have h1 := congr((y_zero $motzkin_sos 0).natDegree)
      rw [Nat.le_zero] at hm3
      simp only [y_zero_sum, y_zero_pow] at h1
      rw [natDegree_sos s_nonempty] at h1
      conv at h1 => left; simp [motzkin, y_zero_apply, aeval_def]
      simp only [Polynomial.natDegree_pow, ← Finset.mul_sup₀, zero_eq_mul, OfNat.ofNat_ne_zero,
        Finset.sup_eq_zero, false_or] at h1
      specialize h1 i hi1
      have : m 0 ∈ (y_zero (g i) 0).support := by
        rw [y_zero_eq_sum_y_zero_monomial]
        simp only [y_zero_monomial_zero]
        rw [Polynomial.mem_support_iff, Polynomial.coeff_sum']
        simp only [Polynomial.coeff_ite]
        rw [Finset.sum_ite, Polynomial.coeff_zero, Finset.sum_const_zero, add_zero]
        simp only [Polynomial.coeff_monomial, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.filter_filter, and_comm]
        have : {x ∈ (g i).support | x 0 = m 0 ∧ x 1 = m 1} = {m} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx1, hx2, hx3⟩
            ext i
            fin_cases i <;> simp <;> assumption
          · intro hx
            simp [hx, hm1, hm3]
        rw [hm3] at this
        simp only [this, Finset.sum_singleton, ← mem_support_iff, hm1]
      simp [Nat.le_zero.mp (h1 ▸ Polynomial.le_natDegree_of_mem_supp _ this)] at hm2
    · have h1 := congr((x_zero $motzkin_sos 0).natDegree)
      rw [Nat.le_zero] at hm2
      simp only [x_zero_sum, x_zero_pow] at h1
      rw [natDegree_sos s_nonempty] at h1
      conv at h1 => left; simp [motzkin, x_zero_apply, aeval_def]
      simp only [Polynomial.natDegree_pow, ← Finset.mul_sup₀, zero_eq_mul, OfNat.ofNat_ne_zero,
        Finset.sup_eq_zero, false_or] at h1
      specialize h1 i hi1
      have : m 1 ∈ (x_zero (g i) 0).support := by
        rw [x_zero_eq_sum_x_zero_monomial]
        simp only [x_zero_monomial_zero]
        rw [Polynomial.mem_support_iff, Polynomial.coeff_sum']
        simp only [Polynomial.coeff_ite]
        rw [Finset.sum_ite, Polynomial.coeff_zero, Finset.sum_const_zero, add_zero]
        simp only [Polynomial.coeff_monomial, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.filter_filter]
        have : {x ∈ (g i).support | x 0 = m 0 ∧ x 1 = m 1} = {m} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx1, hx2, hx3⟩
            ext i
            fin_cases i <;> simp <;> assumption
          · intro hx
            simp [hx, hm1, hm2]
        rw [hm2] at this
        simp only [this, Finset.sum_singleton, ← mem_support_iff, hm1]
      simp [Nat.le_zero.mp (h1 ▸ Polynomial.le_natDegree_of_mem_supp _ this)] at hm3

  let t : Set (Fin 2 →₀ ℕ) := {⟪2, 1⟫, ⟪1, 2⟫, ⟪1, 1⟫, 0}
  have possible_mon : t = {m | m 0 + m 1 ≤ 3 ∧ (0 < m 0 ↔ 0 < m 1)} := by
    ext m
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, t]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      <;> simp
    · rintro ⟨motzkin_sos, h2⟩
      suffices (m 0 = 2 ∧ m 1 = 1) ∨ (m 0 = 1 ∧ m 1 = 2) ∨
          (m 0 = 1 ∧ m 1 = 1) ∨ (m 0 = 0 ∧ m 1 = 0) by
        simpa [Finsupp.ext_iff]
      have : m 0 ≤ 3 := by omega
      have : m 1 ≤ 3 - m 0 := by omega
      interval_cases (m 0)
      <;> interval_cases (m 1)
      <;> (first | contradiction | decide)

  have g_general_form : ∀ i ∈ s, ∃ a b c d, g i = (monomial ⟪2, 1⟫ a) + (monomial ⟪1, 2⟫ b) +
      (monomial ⟪1, 1⟫ c) + (monomial 0 d) := by
    intro i hi
    refine ⟨(g i).coeff ⟪2, 1⟫, (g i).coeff ⟪1, 2⟫, (g i).coeff ⟪1, 1⟫, (g i).coeff 0, ?_⟩
    rw [MvPolynomial.ext_iff]
    intro m
    by_cases! g_general_form : m ∈ t
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, t] at g_general_form
      rcases g_general_form with rfl | rfl | rfl | rfl
      <;> simp [Finsupp.ext_iff]
    · have h6 : (g i).coeff m = 0 := by
        simp only [possible_mon, Set.mem_setOf_eq] at g_general_form
        contrapose! g_general_form
        refine ⟨totalDegree_le_three i hi m (mem_support_iff.mpr g_general_form),
          x_iff_y i hi m (mem_support_iff.mpr g_general_form)⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, t] at g_general_form
      simp [h6, g_general_form, eq_comm]

  have h6 : ∀ i ∈ s, (g i ^ 2).coeff ⟪2, 2⟫ = (g i).coeff ⟪1, 1⟫ ^ 2 := by
    intro i hi
    obtain ⟨a, b, c, d, h6⟩ := g_general_form i hi
    simp only [h6, pow_two, mul_add, add_mul, monomial_mul, coeff_add, coeff_monomial]
    simp [Finsupp.ext_iff]

  replace motzkin_sos := congr(($motzkin_sos).coeff ⟪2, 2⟫)
  rw [coeff_sum, Finset.sum_congr rfl h6] at motzkin_sos
  have : 0 ≤ motzkin (K := K).coeff ⟪2, 2⟫ := by simp [motzkin_sos, Finset.sum_nonneg, sq_nonneg]
  have : 0 > motzkin (K := K).coeff ⟪2, 2⟫ := by simp [motzkin, coeff_one, Finsupp.ext_iff]
  order

#min_imports
