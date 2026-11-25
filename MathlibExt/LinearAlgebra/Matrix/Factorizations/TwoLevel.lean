/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Two-level unitary decomposition

Every finite-dimensional unitary matrix is a product of two-level unitary
matrices. The adjacent-factor form and the exact count follow Kitaev, Shen
and Vyalyi, Classical and Quantum Computation, Lemma 8.2 and formula (8.6).
-/

@[expose] public section

namespace Matrix

/-- A matrix is two-level on the coordinate pair `i, j` when it agrees with
the identity outside the corresponding two-by-two coordinate block. -/
def IsTwoLevel {n α : Type*} [DecidableEq n] [Zero α] [One α]
    (M : Matrix n n α) (i j : n) : Prop :=
  i ≠ j ∧ ∀ k l, (k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j) →
    M k l = (1 : Matrix n n α) k l

/-- Zero vector case of the Fin 2 elimination step. -/
private theorem exists_unitary_fin_two_zero :
    ∃ V ∈ unitaryGroup (Fin 2) ℂ,
      V *ᵥ ![0, 0] =
        ![((Real.sqrt (‖(0 : ℂ)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) : ℝ) : ℂ),
          0] := by
  refine ⟨1, by simp, by simp⟩

/-- The Fin 2 radius is nonzero unless both entries vanish. -/
private theorem fin_two_sqrt_ne_zero {c₁ c₂ : ℂ}
    (h : ¬(c₁ = 0 ∧ c₂ = 0)) :
    Real.sqrt (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2) ≠ 0 := by
  intro hr0
  have hnonneg : 0 ≤ ‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 := by positivity
  have hr2 : (Real.sqrt (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2)) ^ 2 =
      ‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 :=
    Real.sq_sqrt hnonneg
  rw [hr0, zero_pow (by decide : 2 ≠ 0)] at hr2
  have hx0 : ‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 = 0 := hr2.symm
  have hc1 : ‖c₁‖ = 0 := by
    nlinarith [sq_nonneg (‖c₁‖), sq_nonneg (‖c₂‖), hx0]
  have hc2 : ‖c₂‖ = 0 := by
    nlinarith [sq_nonneg (‖c₁‖), sq_nonneg (‖c₂‖), hx0]
  have e1 : c₁ = 0 := norm_eq_zero.mp hc1
  have e2 : c₂ = 0 := norm_eq_zero.mp hc2
  exact h ⟨e1, e2⟩

/-- A two-dimensional unitary sends any vector to a nonnegative multiple of
the first standard basis vector with the same Euclidean length. -/
theorem exists_unitary_fin_two_mulVec_eq (c₁ c₂ : ℂ) :
    ∃ V ∈ unitaryGroup (Fin 2) ℂ,
      V *ᵥ ![c₁, c₂] =
        ![((Real.sqrt (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2) : ℝ) : ℂ), 0] := by
  by_cases h : c₁ = 0 ∧ c₂ = 0
  · obtain ⟨rfl, rfl⟩ := h
    exact exists_unitary_fin_two_zero
  · have hr0 : Real.sqrt (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2) ≠ 0 :=
      fin_two_sqrt_ne_zero h
    set r : ℝ := Real.sqrt (‖c₁‖ ^ 2 + ‖c₂‖ ^ 2) with hr
    set s : ℂ := (r : ℂ) with hs
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact_mod_cast hr0
    have hnonneg : 0 ≤ ‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 := by positivity
    have hr2 : r ^ 2 = ‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 := by
      rw [hr]
      exact Real.sq_sqrt hnonneg
    have hsq : s * s = ((‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (r : ℂ) * (r : ℂ) = (((r ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [hs, hc, hr2]
    have hstar : star s = s := by simp [hs]
    have e1 : star c₁ * c₁ = ((‖c₁‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.conj_mul c₁
    have e2 : star c₂ * c₂ = ((‖c₂‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.conj_mul c₂
    have f1 : c₁ * star c₁ = ((‖c₁‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.mul_conj c₁
    have f2 : c₂ * star c₂ = ((‖c₂‖ ^ 2 : ℝ) : ℂ) := by
      simpa using RCLike.mul_conj c₂
    have hsum0 : ((‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [← hsq]
      exact mul_ne_zero hs0 hs0
    have hcast : ((‖c₁‖ ^ 2 : ℝ) : ℂ) + ((‖c₂‖ ^ 2 : ℝ) : ℂ) =
        ((‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hcast' : ((‖c₂‖ ^ 2 : ℝ) : ℂ) + ((‖c₁‖ ^ 2 : ℝ) : ℂ) =
        ((‖c₁‖ ^ 2 + ‖c₂‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have h2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    refine ⟨!![star c₁ / s, star c₂ / s; -c₂ / s, c₁ / s], ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      rcases h2 i with rfl | rfl <;> rcases h2 j with rfl | rfl <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.one_apply_eq]
      · simp only [star_div₀, star_star, hstar]
        rw [div_mul_div_comm, div_mul_div_comm, e1, e2, hsq, ← add_div, hcast,
          div_self hsum0]
      · rw [Matrix.one_apply_ne h01]
        simp only [star_div₀, star_neg, hstar]
        rw [div_mul_div_comm, div_mul_div_comm, ← add_div,
          show star c₁ * -star c₂ + star c₂ * star c₁ = 0 by ring, zero_div]
      · rw [Matrix.one_apply_ne h10]
        simp only [star_div₀, star_star, hstar]
        rw [div_mul_div_comm, div_mul_div_comm, ← add_div,
          show -c₂ * c₁ + c₁ * c₂ = 0 by ring, zero_div]
      · simp only [star_div₀, star_neg, hstar]
        have n1 : -c₂ * -star c₂ = c₂ * star c₂ := by ring
        rw [div_mul_div_comm, div_mul_div_comm, n1, f2, f1, hsq, ← add_div,
          hcast', div_self hsum0]
    · ext k
      rcases h2 k with rfl | rfl <;>
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, e1, e2, ← add_div, hcast,
          div_eq_iff hs0]
        exact hsq.symm
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          show -c₂ * c₁ + c₁ * c₂ = 0 by ring, zero_div]

/-- Embed a two-by-two matrix at the coordinate pair `i, j`, acting as the
identity elsewhere. -/
private def embedTwoLevel {d : ℕ} (i j : Fin d)
    (V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun k l =>
    if k = i then
      (if l = i then V 0 0 else if l = j then V 0 1 else 0)
    else if k = j then
      (if l = i then V 1 0 else if l = j then V 1 1 else 0)
    else if k = l then 1 else 0

/-- A sum supported on two points. -/
private theorem sum_if_pair {d : ℕ} (i₀ i₁ : Fin d) (hne : i₀ ≠ i₁)
    (a b : ℂ) :
    (∑ k : Fin d, (if k = i₀ then a else if k = i₁ then b else 0)) =
      a + b := by
  have hsub : ({i₀, i₁} : Finset (Fin d)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hvan : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      k ∉ ({i₀, i₁} : Finset (Fin d)) →
      (if k = i₀ then a else if k = i₁ then b else 0) = 0 := by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [ite_eq_right hk.1, ite_eq_right hk.2]
  rw [← Finset.sum_subset hsub hvan, Finset.sum_pair hne]
  simp [Ne.symm hne]

/-- A sum supported on one point. -/
private theorem sum_if_single {d : ℕ} (i : Fin d) (a : ℂ) :
    (∑ k : Fin d, (if k = i then a else 0)) = a := by
  have hsub : ({i} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  have hvan : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      k ∉ ({i} : Finset (Fin d)) → (if k = i then a else 0) = 0 := by
    intro k _ hk
    simp only [Finset.mem_singleton] at hk
    rw [ite_eq_right hk]
  rw [← Finset.sum_subset hsub hvan, Finset.sum_singleton]
  simp

/-- The embedding of a unitary at a coordinate pair is unitary. -/
private theorem embedTwoLevel_mem_unitaryGroup {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ unitaryGroup (Fin 2) ℂ) :
    embedTwoLevel i j V ∈ unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hVV : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hji : j ≠ i := Ne.symm hij
  have e00 : V 0 0 * star (V 0 0) + V 0 1 * star (V 0 1) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hVV
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq] using h
  have e01 : V 0 0 * star (V 1 0) + V 0 1 * star (V 1 1) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hVV
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_ne h01] using h
  have e10 : V 1 0 * star (V 0 0) + V 1 1 * star (V 0 1) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hVV
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_ne h10] using h
  have e11 : V 1 0 * star (V 1 0) + V 1 1 * star (V 1 1) = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hVV
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq] using h
  ext p q
  simp only [Matrix.mul_apply, Matrix.star_apply]
  by_cases hpi : p = i
  · by_cases hpj : p = j
    · exfalso
      exact hij (hpi.symm.trans hpj)
    · by_cases hqi : q = i
      · by_cases hqj : q = j
        · exfalso
          exact hij (hqi.symm.trans hqj)
        · rw [hpi, hqi]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V i k * star (embedTwoLevel i j V i k) =
              (if k = i then V 0 0 * star (V 0 0)
                else if k = j then V 0 1 * star (V 0 1) else 0) := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm]
          rw [sum_if_pair i j hij, e00, Matrix.one_apply_eq]
      · by_cases hqj : q = j
        · rw [hpi, hqj]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V i k * star (embedTwoLevel i j V j k) =
              (if k = i then V 0 0 * star (V 1 0)
                else if k = j then V 0 1 * star (V 1 1) else 0) := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm]
          rw [sum_if_pair i j hij, e01, Matrix.one_apply_ne hij]
        · rw [hpi]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V i k * star (embedTwoLevel i j V q k) =
              0 := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm, Finset.sum_const_zero]
          rw [Matrix.one_apply_ne (Ne.symm hqi)]
  · by_cases hpj : p = j
    · by_cases hqi : q = i
      · by_cases hqj : q = j
        · exfalso
          exact hij (hqi.symm.trans hqj)
        · rw [hpj, hqi]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V j k * star (embedTwoLevel i j V i k) =
              (if k = i then V 1 0 * star (V 0 0)
                else if k = j then V 1 1 * star (V 0 1) else 0) := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm]
          rw [sum_if_pair i j hij, e10, Matrix.one_apply_ne (Ne.symm hij)]
      · by_cases hqj : q = j
        · rw [hpj, hqj]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V j k * star (embedTwoLevel i j V j k) =
              (if k = i then V 1 0 * star (V 1 0)
                else if k = j then V 1 1 * star (V 1 1) else 0) := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm]
          rw [sum_if_pair i j hij, e11, Matrix.one_apply_eq]
        · rw [hpj]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V j k * star (embedTwoLevel i j V q k) =
              0 := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm, Finset.sum_const_zero]
          rw [Matrix.one_apply_ne (Ne.symm hqj)]
    · by_cases hqi : q = i
      · by_cases hqj : q = j
        · exfalso
          exact hij (hqi.symm.trans hqj)
        · rw [hqi]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V p k * star (embedTwoLevel i j V i k) =
              0 := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm, Finset.sum_const_zero]
          rw [Matrix.one_apply_ne hpi]
      · by_cases hqj : q = j
        · rw [hqj]
          have hterm : ∀ k : Fin d,
              embedTwoLevel i j V p k * star (embedTwoLevel i j V j k) =
              0 := by
            intro k
            simp only [embedTwoLevel]
            by_cases hki : k = i
            · simp_all
            · by_cases hkj : k = j
              · simp_all
              · simp_all
          simp only [hterm, Finset.sum_const_zero]
          rw [Matrix.one_apply_ne hpj]
        · have hterm : ∀ k : Fin d,
              embedTwoLevel i j V p k * star (embedTwoLevel i j V q k) =
              (if k = p then star (if q = p then (1 : ℂ) else 0)
                else 0) := by
            intro k
            simp only [embedTwoLevel]
            by_cases hkp : k = p
            · rw [hkp]
              simp_all
            · have hpk : p ≠ k := fun h => hkp h.symm
              simp_all
          simp only [hterm]
          rw [sum_if_single]
          by_cases hqp : q = p
          · rw [hqp]
            simp [Matrix.one_apply_eq]
          · have hpq : p ≠ q := fun h => hqp h.symm
            rw [ite_eq_right hqp, star_zero, Matrix.one_apply_ne hpq]

/-- Off-block entries of the embedding agree with the identity. -/
private theorem embedTwoLevel_apply_of_ne {d : ℕ} {i j : Fin d}
    {V : Matrix (Fin 2) (Fin 2) ℂ} {k l : Fin d}
    (hki : k ≠ i) (hkj : k ≠ j) :
    embedTwoLevel i j V k l = (1 : Matrix (Fin d) (Fin d) ℂ) k l := by
  simp only [embedTwoLevel]
  rw [ite_eq_right hki, ite_eq_right hkj]
  by_cases hkl : k = l
  · rw [hkl]
    simp [Matrix.one_apply_eq]
  · rw [ite_eq_right hkl, Matrix.one_apply_ne hkl]

/-- The embedding is two-level on its coordinate pair. -/
private theorem embedTwoLevel_isTwoLevel {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    (embedTwoLevel i j V).IsTwoLevel i j := by
  have hji : j ≠ i := Ne.symm hij
  unfold Matrix.IsTwoLevel
  refine ⟨hij, fun k l h => ?_⟩
  rcases h with ⟨hki, hkj⟩ | ⟨hli, hlj⟩
  · exact embedTwoLevel_apply_of_ne hki hkj
  · by_cases hki : k = i
    · rw [hki]
      simp only [embedTwoLevel]
      simp [hli, hlj, Matrix.one_apply_ne (Ne.symm hli)]
    · by_cases hkj : k = j
      · rw [hkj]
        simp only [embedTwoLevel]
        simp [hji, hli, hlj, Matrix.one_apply_ne (Ne.symm hlj)]
      · exact embedTwoLevel_apply_of_ne hki hkj

/-- The embedding acts by the first row of `V` on the first coordinate. -/
private theorem embedTwoLevel_mulVec_row_i {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) {V : Matrix (Fin 2) (Fin 2) ℂ} (x : Fin d → ℂ) :
    ((embedTwoLevel i j V) *ᵥ x) i = V 0 0 * x i + V 0 1 * x j := by
  have hji : j ≠ i := Ne.symm hij
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin d,
      embedTwoLevel i j V i l * x l =
      (if l = i then V 0 0 * x i
        else if l = j then V 0 1 * x j else 0) := by
    intro l
    simp only [embedTwoLevel]
    by_cases hli : l = i
    · simp_all
    · by_cases hlj : l = j
      · simp_all
      · simp_all
  simp only [hterm]
  rw [sum_if_pair i j hij]

/-- The embedding acts by the second row of `V` on the second coordinate. -/
private theorem embedTwoLevel_mulVec_row_j {d : ℕ} {i j : Fin d}
    (hij : i ≠ j) {V : Matrix (Fin 2) (Fin 2) ℂ} (x : Fin d → ℂ) :
    ((embedTwoLevel i j V) *ᵥ x) j = V 1 0 * x i + V 1 1 * x j := by
  have hji : j ≠ i := Ne.symm hij
  simp only [Matrix.mulVec, dotProduct]
  have hterm : ∀ l : Fin d,
      embedTwoLevel i j V j l * x l =
      (if l = i then V 1 0 * x i
        else if l = j then V 1 1 * x j else 0) := by
    intro l
    simp only [embedTwoLevel]
    by_cases hli : l = i
    · simp_all
    · by_cases hlj : l = j
      · simp_all
      · simp_all
  simp only [hterm]
  rw [sum_if_pair i j hij]

/-- The embedding fixes every other coordinate of the vector. -/
private theorem embedTwoLevel_mulVec_row_else {d : ℕ} {i j : Fin d}
    {V : Matrix (Fin 2) (Fin 2) ℂ} (x : Fin d → ℂ) {k : Fin d}
    (hki : k ≠ i) (hkj : k ≠ j) :
    ((embedTwoLevel i j V) *ᵥ x) k = x k := by
  simp only [Matrix.mulVec, dotProduct]
  have hrow : ∀ l : Fin d,
      embedTwoLevel i j V k l = (if k = l then (1 : ℂ) else 0) := by
    intro l
    simp only [embedTwoLevel, ite_eq_right hki, ite_eq_right hkj]
  have hterm : ∀ l : Fin d,
      (if k = l then (1 : ℂ) else 0) * x l = (if l = k then x k else 0) := by
    intro l
    by_cases hlk : l = k
    · rw [hlk]
      simp
    · have hkl : k ≠ l := fun h => hlk h.symm
      simp_all
  simp only [hrow, hterm]
  rw [sum_if_single]

/-- Adjacent indices in `Fin d` are distinct. -/
private theorem adjacent_ne {d s : ℕ} (hs : s + 1 < d) :
    (⟨s, by omega⟩ : Fin d) ≠ ⟨s + 1, hs⟩ := by
  intro h
  have hv : s = s + 1 := congrArg Fin.val h
  omega

/-- The adjacent embedding of a unitary is unitary. -/
private theorem embedAdjacent_mem_unitaryGroup {d s : ℕ} (hs : s + 1 < d)
    {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V ∈ unitaryGroup (Fin 2) ℂ) :
    embedTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ V ∈ unitaryGroup (Fin d) ℂ :=
  embedTwoLevel_mem_unitaryGroup (adjacent_ne hs) hV

/-- The adjacent embedding is two-level on its adjacent pair. -/
private theorem embedAdjacent_isTwoLevel {d s : ℕ} (hs : s + 1 < d)
    (V : Matrix (Fin 2) (Fin 2) ℂ) :
    (embedTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ V).IsTwoLevel
      ⟨s, by omega⟩ ⟨s + 1, hs⟩ :=
  embedTwoLevel_isTwoLevel (adjacent_ne hs) V

private theorem tlp_val_ne_zero {n : ℕ} {k : Fin (n + 1)} (hk : k ≠ 0) :
    k.val ≠ 0 := by
  intro hv
  apply hk
  rw [Fin.ext_iff, hv]
  exact (Fin.val_zero _).symm

private theorem tlp_fin_two_apply_zero (V : Matrix (Fin 2) (Fin 2) ℂ)
    (a b ρ : ℂ) (hVeq : V *ᵥ ![a, b] = ![ρ, 0]) :
    V 0 0 * a + V 0 1 * b = ρ := by
  have h0 := congrArg (fun x : Fin 2 → ℂ => x 0) hVeq
  simpa [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h0

private theorem tlp_fin_two_apply_one (V : Matrix (Fin 2) (Fin 2) ℂ)
    (a b ρ : ℂ) (hVeq : V *ᵥ ![a, b] = ![ρ, 0]) :
    V 1 0 * a + V 1 1 * b = 0 := by
  have h1 := congrArg (fun x : Fin 2 → ℂ => x 1) hVeq
  simpa [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h1

private theorem tlp_mul_eq_mulVec_apply {d : ℕ}
    (G W : Matrix (Fin d) (Fin d) ℂ) (k l : Fin d) :
    (G * W) k l = (G *ᵥ fun m => W m l) k := by
  simp [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum]

private theorem tlp_mul_row_i {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {V : Matrix (Fin 2) (Fin 2) ℂ} (W : Matrix (Fin d) (Fin d) ℂ)
    (l : Fin d) :
    ((embedTwoLevel i j V) * W) i l = V 0 0 * W i l + V 0 1 * W j l := by
  rw [tlp_mul_eq_mulVec_apply]
  exact embedTwoLevel_mulVec_row_i hij _

private theorem tlp_mul_row_j {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    {V : Matrix (Fin 2) (Fin 2) ℂ} (W : Matrix (Fin d) (Fin d) ℂ)
    (l : Fin d) :
    ((embedTwoLevel i j V) * W) j l = V 1 0 * W i l + V 1 1 * W j l := by
  rw [tlp_mul_eq_mulVec_apply]
  exact embedTwoLevel_mulVec_row_j hij _

private theorem tlp_mul_row_else {d : ℕ} {i j : Fin d}
    {V : Matrix (Fin 2) (Fin 2) ℂ} (W : Matrix (Fin d) (Fin d) ℂ)
    {k : Fin d} (l : Fin d) (hki : k ≠ i) (hkj : k ≠ j) :
    ((embedTwoLevel i j V) * W) k l = W k l := by
  rw [tlp_mul_eq_mulVec_apply]
  exact embedTwoLevel_mulVec_row_else _ hki hkj

private theorem tlp_count_add (e : ℕ) (he : 2 ≤ e) :
    e + e * (e - 1) / 2 = (e + 1) * e / 2 := by
  have key : (e + 1) * e = e * (e - 1) + e * 2 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
    have hsub : f + 2 - 1 = f + 1 := by omega
    rw [hsub]
    ring
  have hdiv : (e * (e - 1) + e * 2) / 2 = e * (e - 1) / 2 + e :=
    Nat.add_mul_div_right _ _ (by norm_num)
  rw [key, hdiv, Nat.add_comm]

private theorem tlp_fin_two_eq (k : Fin 2) : k = 0 ∨ k = 1 := by
  have h2 := k.isLt
  have hvo : k.val = 0 ∨ k.val = 1 := by omega
  rcases hvo with h0 | h1
  · refine Or.inl (Fin.ext ?_)
    rw [h0]
    exact (Fin.val_zero 2).symm
  · refine Or.inr (Fin.ext ?_)
    rw [h1]
    rfl

private theorem tlp_isTwoLevel_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.IsTwoLevel 0 1 := by
  refine ⟨by decide, fun k l h => ?_⟩
  have hk := tlp_fin_two_eq k
  have hl := tlp_fin_two_eq l
  rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp at h

private theorem tlp_base_two (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ unitaryGroup (Fin 2) ℂ) :
    ∃ L : List (Matrix (Fin 2) (Fin 2) ℂ),
      L.length = 2 * (2 - 1) / 2 ∧
      (∀ M ∈ L, M ∈ unitaryGroup (Fin 2) ℂ ∧
        ∃ (s : ℕ) (hs : s + 1 < 2),
          M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
      L.prod = U := by
  refine ⟨[U], by norm_num, ?_, by simp⟩
  intro M hM
  simp only [List.mem_singleton] at hM
  subst hM
  refine ⟨hU, 0, by norm_num, ?_⟩
  exact tlp_isTwoLevel_fin_two _

private def tlpLift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun k l =>
    if hk : k = 0 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l
    else if hl : l = 0 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l
    else M (k.pred hk) (l.pred hl)

private theorem tlpLift_def {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (k l : Fin (n + 1)) :
    tlpLift M k l =
      (if hk : k = 0 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l
      else if hl : l = 0 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l
      else M (k.pred hk) (l.pred hl)) :=
  rfl

private theorem tlpLift_zero_row {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (l : Fin (n + 1)) :
    tlpLift M 0 l = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 l := by
  rw [tlpLift_def, dite_eq_left rfl]

private theorem tlpLift_zero_col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {k : Fin (n + 1)} (hk : k ≠ 0) :
    tlpLift M k 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k 0 := by
  rw [tlpLift_def, dite_eq_right hk, dite_eq_left rfl]

private theorem tlpLift_of_ne {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {k l : Fin (n + 1)} (hk : k ≠ 0) (hl : l ≠ 0) :
    tlpLift M k l = M (k.pred hk) (l.pred hl) := by
  rw [tlpLift_def, dite_eq_right hk, dite_eq_right hl]

private theorem tlpLift_col_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (k : Fin (n + 1)) :
    tlpLift M k 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k 0 := by
  by_cases hk : k = 0
  · subst hk
    exact tlpLift_zero_row M 0
  · exact tlpLift_zero_col M hk

private theorem tlp_one_pred_congr {n : ℕ} {k l : Fin (n + 1)} (hk : k ≠ 0)
    (hl : l ≠ 0) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (k.pred hk) (l.pred hl) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k l := by
  by_cases hkl : k = l
  · subst hkl
    have hpp : k.pred hk = k.pred hl := rfl
    rw [hpp, Matrix.one_apply_eq, Matrix.one_apply_eq]
  · have hne : k.pred hk ≠ l.pred hl := by
      intro hcon
      apply hkl
      have h2 := congrArg Fin.succ hcon
      rwa [Fin.succ_pred, Fin.succ_pred] at h2
    rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hkl]

private theorem tlpLift_one {n : ℕ} :
    tlpLift (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  apply Matrix.ext_iff.mp
  intro k l
  by_cases hk : k = 0
  · subst hk
    rw [tlpLift_zero_row]
  · by_cases hl : l = 0
    · subst hl
      rw [tlpLift_zero_col _ hk]
    · rw [tlpLift_of_ne _ hk hl]
      exact tlp_one_pred_congr hk hl

private theorem tlpLift_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) :
    tlpLift (M * N) = tlpLift M * tlpLift N := by
  apply Matrix.ext_iff.mp
  intro k l
  by_cases hk : k = 0
  · subst hk
    rw [tlpLift_zero_row, Matrix.mul_apply]
    symm
    have h0 : ∀ k' : Fin (n + 1), tlpLift M 0 k' * tlpLift N k' l =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 k' * tlpLift N k' l := by
      intro k'
      rw [tlpLift_zero_row]
    rw [Finset.sum_congr rfl (fun k' _ => h0 k')]
    have hsingle := Finset.sum_eq_single (a := (0 : Fin (n + 1)))
      (s := Finset.univ)
      (f := fun k' => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 k' *
        tlpLift N k' l)
      (fun k' _ hk' => by rw [Matrix.one_apply_ne (Ne.symm hk'), zero_mul])
      (fun hcon => absurd (Finset.mem_univ 0) hcon)
    rw [hsingle, Matrix.one_apply_eq, one_mul, tlpLift_zero_row]
  · by_cases hl : l = 0
    · subst hl
      rw [tlpLift_col_zero, Matrix.mul_apply]
      symm
      have h0 : ∀ k' : Fin (n + 1), tlpLift M k k' * tlpLift N k' 0 =
          tlpLift M k k' * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0 := by
        intro k'
        rw [tlpLift_col_zero]
      rw [Finset.sum_congr rfl (fun k' _ => h0 k')]
      have hsingle := Finset.sum_eq_single (a := (0 : Fin (n + 1)))
        (s := Finset.univ)
        (f := fun k' => tlpLift M k k' *
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0)
        (fun k' _ hk' => by rw [Matrix.one_apply_ne hk', mul_zero])
        (fun hcon => absurd (Finset.mem_univ 0) hcon)
      rw [hsingle, Matrix.one_apply_eq, mul_one]
      exact tlpLift_col_zero M k
    · rw [tlpLift_of_ne _ hk hl, Matrix.mul_apply, Matrix.mul_apply]
      rw [Fin.sum_univ_succ]
      have hz : tlpLift M k 0 * tlpLift N 0 l = 0 := by
        rw [tlpLift_col_zero, Matrix.one_apply_ne hk, zero_mul]
      rw [hz, zero_add]
      apply Finset.sum_congr rfl
      intro i _
      have hsi : i.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero i
      rw [tlpLift_of_ne _ hk hsi, tlpLift_of_ne _ hsi hl, Fin.pred_succ]

private theorem tlpLift_prod {n : ℕ} (L : List (Matrix (Fin n) (Fin n) ℂ)) :
    (L.map tlpLift).prod = tlpLift L.prod := by
  induction L with
  | nil => simp [tlpLift_one]
  | cons M L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, tlpLift_mul]

private theorem tlpLift_mem_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : M ∈ unitaryGroup (Fin n) ℂ) :
    tlpLift M ∈ unitaryGroup (Fin (n + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  apply Matrix.ext_iff.mp
  intro k l
  rw [Matrix.mul_apply]
  by_cases hk : k = 0
  · subst hk
    have h0 : ∀ k' : Fin (n + 1),
        star (tlpLift M) 0 k' * tlpLift M k' l =
          star ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0) *
            tlpLift M k' l := by
      intro k'
      rw [Matrix.star_apply, tlpLift_col_zero]
    rw [Finset.sum_congr rfl (fun k' _ => h0 k')]
    have hsingle := Finset.sum_eq_single (a := (0 : Fin (n + 1)))
      (s := Finset.univ)
      (f := fun k' => star ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0) *
        tlpLift M k' l)
      (fun k' _ hk' => by rw [Matrix.one_apply_ne hk', star_zero, zero_mul])
      (fun hcon => absurd (Finset.mem_univ 0) hcon)
    rw [hsingle, Matrix.one_apply_eq, star_one, one_mul, tlpLift_zero_row]
  · by_cases hl : l = 0
    · subst hl
      have h0 : ∀ k' : Fin (n + 1),
          star (tlpLift M) k k' * tlpLift M k' 0 =
            star (tlpLift M k' k) *
              (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0 := by
        intro k'
        rw [Matrix.star_apply, tlpLift_col_zero]
      rw [Finset.sum_congr rfl (fun k' _ => h0 k')]
      have hsingle := Finset.sum_eq_single (a := (0 : Fin (n + 1)))
        (s := Finset.univ)
        (f := fun k' => star (tlpLift M k' k) *
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) k' 0)
        (fun k' _ hk' => by rw [Matrix.one_apply_ne hk', mul_zero])
        (fun hcon => absurd (Finset.mem_univ 0) hcon)
      rw [hsingle, tlpLift_zero_row, Matrix.one_apply_ne (Ne.symm hk),
        star_zero, zero_mul, Matrix.one_apply_ne hk]
    · have hmem : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.mp hM
      have h0 : ∀ k' : Fin (n + 1),
          star (tlpLift M) k k' * tlpLift M k' l =
            star (tlpLift M k' k) * tlpLift M k' l := by
        intro k'
        rw [Matrix.star_apply]
      rw [Finset.sum_congr rfl (fun k' _ => h0 k'), Fin.sum_univ_succ]
      have hz : star (tlpLift M 0 k) * tlpLift M 0 l = 0 := by
        rw [tlpLift_zero_row, tlpLift_zero_row,
          Matrix.one_apply_ne (Ne.symm hk), star_zero, zero_mul]
      rw [hz, zero_add]
      have hterm : ∀ i : Fin n,
          star (tlpLift M i.succ k) * tlpLift M i.succ l =
            star M (k.pred hk) i * M i (l.pred hl) := by
        intro i
        have hsi : i.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero i
        rw [tlpLift_of_ne _ hsi hk, tlpLift_of_ne _ hsi hl, Fin.pred_succ,
          Matrix.star_apply]
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      have hfin := congrArg
        (fun N : Matrix (Fin n) (Fin n) ℂ => N (k.pred hk) (l.pred hl)) hmem
      rw [Matrix.mul_apply] at hfin
      rw [hfin]
      exact tlp_one_pred_congr hk hl

private theorem tlpLift_isTwoLevel {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {s : ℕ} (hs : s + 1 < n)
    (hM : M.IsTwoLevel (⟨s, by omega⟩ : Fin n) ⟨s + 1, hs⟩) :
    (tlpLift M).IsTwoLevel (⟨s + 1, by omega⟩ : Fin (n + 1))
      ⟨s + 1 + 1, by omega⟩ := by
  have hne : (⟨s + 1, by omega⟩ : Fin (n + 1)) ≠ ⟨s + 1 + 1, by omega⟩ := by
    intro hcon
    have hv : s + 1 = s + 1 + 1 := congrArg Fin.val hcon
    omega
  refine ⟨hne, fun k l h => ?_⟩
  by_cases hk : k = 0
  · subst hk
    exact tlpLift_zero_row M l
  · by_cases hl : l = 0
    · subst hl
      exact tlpLift_zero_col M hk
    · rw [tlpLift_of_ne M hk hl]
      have hside : (k.pred hk ≠ (⟨s, by omega⟩ : Fin n) ∧
            k.pred hk ≠ ⟨s + 1, hs⟩) ∨
          (l.pred hl ≠ (⟨s, by omega⟩ : Fin n) ∧
            l.pred hl ≠ ⟨s + 1, hs⟩) := by
        rcases h with ⟨hka, hkb⟩ | ⟨hla, hlb⟩
        · refine Or.inl ⟨?_, ?_⟩
          · intro hcon
            apply hka
            have h2 := congrArg Fin.succ hcon
            rw [Fin.succ_pred] at h2
            exact h2
          · intro hcon
            apply hkb
            have h2 := congrArg Fin.succ hcon
            rw [Fin.succ_pred] at h2
            exact h2
        · refine Or.inr ⟨?_, ?_⟩
          · intro hcon
            apply hla
            have h2 := congrArg Fin.succ hcon
            rw [Fin.succ_pred] at h2
            exact h2
          · intro hcon
            apply hlb
            have h2 := congrArg Fin.succ hcon
            rw [Fin.succ_pred] at h2
            exact h2
      have hM2 := hM.2 _ _ hside
      rw [hM2]
      exact tlp_one_pred_congr hk hl

private theorem tlp_coe_inv_unitary {d : ℕ} (g : unitaryGroup (Fin d) ℂ) :
    ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) =
      star (g : Matrix (Fin d) (Fin d) ℂ) := by
  have hmem : (g : Matrix (Fin d) (Fin d) ℂ) *
      star (g : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp g.property
  have hinv : ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
      (g : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    have h : ((((g⁻¹ * g : unitaryGroup (Fin d) ℂ))) :
        Matrix (Fin d) (Fin d) ℂ) =
        ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
          (g : Matrix (Fin d) (Fin d) ℂ) := rfl
    rw [← h, inv_mul_cancel]
    rfl
  calc ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      = ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) * 1 :=
        (mul_one _).symm
    _ = ((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
        ((g : Matrix (Fin d) (Fin d) ℂ) *
          star (g : Matrix (Fin d) (Fin d) ℂ)) := by rw [hmem, mul_one]
    _ = (((g⁻¹ : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
        (g : Matrix (Fin d) (Fin d) ℂ)) *
        star (g : Matrix (Fin d) (Fin d) ℂ) := by rw [mul_assoc]
    _ = star (g : Matrix (Fin d) (Fin d) ℂ) := by rw [hinv, one_mul]

private theorem tlp_inv_isTwoLevel {d : ℕ} (g : unitaryGroup (Fin d) ℂ)
    (i j : Fin d) (h : (g : Matrix (Fin d) (Fin d) ℂ).IsTwoLevel i j) :
    (((g⁻¹ : unitaryGroup (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ).IsTwoLevel i j := by
  rw [tlp_coe_inv_unitary]
  refine ⟨h.1, fun k l hkl => ?_⟩
  rw [Matrix.star_apply]
  have h1 : (g : Matrix (Fin d) (Fin d) ℂ) l k =
      (1 : Matrix (Fin d) (Fin d) ℂ) l k :=
    h.2 l k hkl.symm
  rw [h1]
  by_cases hlk : l = k
  · subst hlk
    rw [Matrix.one_apply_eq, star_one]
  · rw [Matrix.one_apply_ne hlk, Matrix.one_apply_ne (Ne.symm hlk), star_zero]

private theorem tlp_invGs_prod {d : ℕ} (Gs : List (Matrix (Fin d) (Fin d) ℂ))
    (hall : ∀ G ∈ Gs, G ∈ unitaryGroup (Fin d) ℂ) :
    ∃ invGs : List (Matrix (Fin d) (Fin d) ℂ),
      invGs.length = Gs.length ∧
      (∀ M ∈ invGs, ∃ G ∈ Gs, ∃ hG : G ∈ unitaryGroup (Fin d) ℂ,
        M = ((⟨G, hG⟩⁻¹ : unitaryGroup (Fin d) ℂ) :
          Matrix (Fin d) (Fin d) ℂ)) ∧
      invGs.prod * Gs.reverse.prod = 1 := by
  induction Gs with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons G Gs ih =>
    have hG : G ∈ unitaryGroup (Fin d) ℂ := hall G (by simp)
    have hall' : ∀ G' ∈ Gs, G' ∈ unitaryGroup (Fin d) ℂ :=
      fun G' h => hall G' (by simp [h])
    obtain ⟨invGs, hlen, hmem, hprod⟩ := ih hall'
    refine ⟨((⟨G, hG⟩⁻¹ : unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) :: invGs, by simp [hlen], ?_, ?_⟩
    · intro M hM
      simp only [List.mem_cons] at hM
      rcases hM with rfl | hM
      · exact ⟨G, by simp, hG, rfl⟩
      · obtain ⟨G', hG'mem, hG', rfl⟩ := hmem M hM
        exact ⟨G', by simp [hG'mem], hG', rfl⟩
    · simp only [List.prod_cons]
      have hrev : (G :: Gs).reverse.prod = Gs.reverse.prod * G := by
        have heq : (G :: Gs) = [G] ++ Gs := rfl
        rw [heq, List.reverse_append, List.reverse_singleton, List.prod_append]
        simp
      rw [hrev]
      have hassoc : ∀ (a b c e : Matrix (Fin d) (Fin d) ℂ),
          (a * b) * (c * e) = a * ((b * c) * e) := by
        intro a b c e
        rw [mul_assoc a b _, ← mul_assoc b c e]
      rw [hassoc, hprod, one_mul]
      have h : ((((⟨G, hG⟩⁻¹ * ⟨G, hG⟩ : unitaryGroup (Fin d) ℂ))) :
          Matrix (Fin d) (Fin d) ℂ) =
          ((⟨G, hG⟩⁻¹ : unitaryGroup (Fin d) ℂ) :
            Matrix (Fin d) (Fin d) ℂ) * G := rfl
      rw [← h, inv_mul_cancel]
      rfl

private theorem tlp_step (n : ℕ) (hn : 2 ≤ n)
    (IH : ∀ W : Matrix (Fin n) (Fin n) ℂ, W ∈ unitaryGroup (Fin n) ℂ →
      ∃ L : List (Matrix (Fin n) (Fin n) ℂ),
        L.length = n * (n - 1) / 2 ∧
        (∀ M ∈ L, M ∈ unitaryGroup (Fin n) ℂ ∧
          ∃ (s : ℕ) (hs : s + 1 < n),
            M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
        L.prod = W)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hU : U ∈ unitaryGroup (Fin (n + 1)) ℂ) :
    ∃ L : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      L.length = (n + 1) * ((n + 1) - 1) / 2 ∧
      (∀ M ∈ L, M ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
        ∃ (s : ℕ) (hs : s + 1 < n + 1),
          M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
      L.prod = U := by
  have elim : ∀ t : ℕ, t ≤ n →
      ∃ (Gs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
        (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
        Gs.length = t ∧
        (∀ G ∈ Gs, G ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
          ∃ (s : ℕ) (hs : s + 1 < n + 1),
            G.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
        W = Gs.reverse.prod * U ∧
        W ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
        (∀ k : Fin (n + 1), n + 1 - t ≤ k.val → W k 0 = 0) ∧
        (t < n → W 0 0 = U 0 0) ∧
        (t = n → ∃ ρ : ℝ, 0 ≤ ρ ∧ W 0 0 = ((ρ : ℝ) : ℂ)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨[], U, rfl, by simp, by simp, hU, ?_, ?_, ?_⟩
      · intro k hk
        have hlt := k.isLt
        omega
      · intro _
        rfl
      · intro hcon
        omega
    | succ t ih =>
      intro ht
      obtain ⟨Gs, W, hlen, hval, hW, hWu, hclr, hrow0, hfin⟩ := ih (by omega)
      obtain ⟨s', hs'⟩ : ∃ s', n - t = s' + 1 := ⟨n - t - 1, by omega⟩
      have hGs : s' + 1 < n + 1 := by omega
      set iA : Fin (n + 1) := ⟨s', by omega⟩ with hiAdef
      set jA : Fin (n + 1) := ⟨s' + 1, hGs⟩ with hjAdef
      have hiAval : iA.val = s' := rfl
      have hjAval : jA.val = s' + 1 := rfl
      have hij : iA ≠ jA := adjacent_ne hGs
      obtain ⟨V, hV, hVeq⟩ := exists_unitary_fin_two_mulVec_eq (W iA 0) (W jA 0)
      have hfst := tlp_fin_two_apply_zero V _ _ _ hVeq
      have hsnd := tlp_fin_two_apply_one V _ _ _ hVeq
      set G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
        embedTwoLevel iA jA V with hGdef
      have hGmem : G ∈ unitaryGroup (Fin (n + 1)) ℂ :=
        embedAdjacent_mem_unitaryGroup hGs hV
      have hG2l : G.IsTwoLevel iA jA := embedAdjacent_isTwoLevel hGs V
      have hGval : G ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
          ∃ (s : ℕ) (hs : s + 1 < n + 1),
            G.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ :=
        ⟨hGmem, s', hGs, hG2l⟩
      refine ⟨Gs ++ [G], G * W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [List.length_append, hlen]
      · intro M hM
        rw [List.mem_append, List.mem_singleton] at hM
        rcases hM with hM | hM
        · exact hval M hM
        · subst hM
          exact hGval
      · have hrev : (Gs ++ [G]).reverse.prod = G * Gs.reverse.prod := by
          rw [List.reverse_append, List.reverse_singleton, List.prod_append]
          simp
        rw [hrev, hW, mul_assoc]
      · exact mul_mem hGmem hWu
      · intro k hk
        have hks : s' + 1 ≤ k.val := by omega
        by_cases hkk : k = jA
        · subst hkk
          have hrow : (G * W) jA 0 = V 1 0 * W iA 0 + V 1 1 * W jA 0 :=
            tlp_mul_row_j (i := iA) (j := jA) hij W 0
          rw [hrow]
          exact hsnd
        · have hki : k ≠ iA := by
            intro hcon
            have hv : k.val = iA.val := congrArg Fin.val hcon
            omega
          have hrow : (G * W) k 0 = W k 0 :=
            tlp_mul_row_else (i := iA) (j := jA) W 0 hki hkk
          rw [hrow]
          apply hclr k
          have hne : k.val ≠ s' + 1 := by
            intro hcon
            apply hkk
            apply Fin.ext
            rw [hjAval]
            exact hcon
          omega
      · intro hlt
        have hs2 : 2 ≤ s' + 1 := by omega
        have h0i : (0 : Fin (n + 1)) ≠ iA := by
          have hne : (0 : Fin (n + 1)).val ≠ iA.val := by
            have h0v : (0 : Fin (n + 1)).val = 0 := Fin.val_zero _
            omega
          exact fun hcon => hne (congrArg Fin.val hcon)
        have h0j : (0 : Fin (n + 1)) ≠ jA := by
          have hne : (0 : Fin (n + 1)).val ≠ jA.val := by
            have h0v : (0 : Fin (n + 1)).val = 0 := Fin.val_zero _
            omega
          exact fun hcon => hne (congrArg Fin.val hcon)
        have hrow : (G * W) 0 0 = W 0 0 :=
          tlp_mul_row_else (i := iA) (j := jA) W 0 h0i h0j
        rw [hrow]
        exact hrow0 (by omega)
      · intro htn
        have hs1 : s' + 1 = 1 := by omega
        have hs0 : s' = 0 := by omega
        subst hs0
        refine ⟨Real.sqrt (‖W iA 0‖ ^ 2 + ‖W jA 0‖ ^ 2),
          Real.sqrt_nonneg _, ?_⟩
        have h0eq : (0 : Fin (n + 1)) = iA := by
          apply Fin.ext
          rw [hiAval]
          exact Fin.val_zero _
        have hstep : (G * W) 0 0 = (G * W) iA 0 := by rw [h0eq]
        have hrow : (G * W) iA 0 = V 0 0 * W iA 0 + V 0 1 * W jA 0 :=
          tlp_mul_row_i (i := iA) (j := jA) hij W 0
        rw [hstep, hrow]
        exact hfst
  obtain ⟨Gs, W, hlen, hval, hW, hWu, hclr, hrow0, hfin⟩ := elim n le_rfl
  obtain ⟨ρ, hρnonneg, hρeq⟩ := hfin rfl
  have hstarW : star W * W = 1 := Matrix.mem_unitaryGroup_iff'.mp hWu
  have hclr0 : ∀ k : Fin (n + 1), k ≠ 0 → W k 0 = 0 := by
    intro k hk
    apply hclr k
    have hlt := k.isLt
    have hv : k.val ≠ 0 := tlp_val_ne_zero hk
    omega
  have hnorm : ‖W 0 0‖ ^ 2 = 1 := by
    have h00 := congrArg
      (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M 0 0) hstarW
    rw [Matrix.mul_apply] at h00
    have hsum : (∑ k : Fin (n + 1), star W 0 k * W k 0) =
        star (W 0 0) * W 0 0 := by
      apply Finset.sum_eq_single 0
      · intro k _ hk0
        rw [hclr0 k hk0, mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ 0) hcon
    rw [hsum] at h00
    have hsq := Complex.conj_mul' (W 0 0)
    rw [show star (W 0 0) = (starRingEnd ℂ) (W 0 0) from rfl, hsq,
      Matrix.one_apply_eq] at h00
    exact_mod_cast h00
  have hρ1 : ρ = 1 := by
    have hnormρ : ‖W 0 0‖ = ρ := by
      rw [hρeq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρnonneg]
    rw [hnormρ] at hnorm
    nlinarith
  have hW00 : W 0 0 = 1 := by
    rw [hρeq, hρ1, Complex.ofReal_one]
  have hWrow0 : ∀ j : Fin (n + 1),
      W 0 j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 j := by
    intro j
    have hstar : star W j 0 =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) j 0 := by
      have hj0 := congrArg
        (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => M j 0) hstarW
      rw [Matrix.mul_apply] at hj0
      have hsum : (∑ k : Fin (n + 1), star W j k * W k 0) =
          star W j 0 * W 0 0 := by
        apply Finset.sum_eq_single 0
        · intro k _ hk0
          rw [hclr0 k hk0, mul_zero]
        · intro hcon
          exact absurd (Finset.mem_univ 0) hcon
      rw [hsum, hW00, mul_one] at hj0
      exact hj0
    have hconj : W 0 j = (starRingEnd ℂ) (star W j 0) := by
      have hsa := Matrix.star_apply W j 0
      rw [hsa, show star (W 0 j) = (starRingEnd ℂ) (W 0 j) from rfl,
        Complex.conj_conj]
    rw [hconj, hstar]
    by_cases hj : j = 0
    · subst hj
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hj, Matrix.one_apply_ne (Ne.symm hj)]
      simp
  set WBlk : Matrix (Fin n) (Fin n) ℂ :=
    fun i j => W i.succ j.succ with hWBlkdef
  have hWBlku : WBlk ∈ unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply Matrix.ext_iff.mp
    intro i j
    rw [Matrix.mul_apply]
    have hWij := congrArg
      (fun N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => N i.succ j.succ) hstarW
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hWij
    have hz : star W i.succ 0 * W 0 j.succ = 0 := by
      rw [hWrow0, Matrix.one_apply_ne (Ne.symm (Fin.succ_ne_zero j)), mul_zero]
    rw [hz, zero_add] at hWij
    have hterm : ∀ a : Fin n, star WBlk i a * WBlk a j =
        star W i.succ a.succ * W a.succ j.succ := by
      intro a
      have e1 : WBlk a i = W a.succ i.succ := rfl
      have e2 : WBlk a j = W a.succ j.succ := rfl
      rw [Matrix.star_apply, e1, e2, Matrix.star_apply]
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    rw [hWij]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have hne : i.succ ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]
  obtain ⟨Lih, hlenih, hvalih, hprodih⟩ := IH WBlk hWBlku
  have hblock : W = tlpLift WBlk := by
    apply Matrix.ext_iff.mp
    intro k l
    by_cases hk : k = 0
    · subst hk
      rw [tlpLift_zero_row]
      exact hWrow0 l
    · by_cases hl : l = 0
      · subst hl
        rw [tlpLift_col_zero, Matrix.one_apply_ne hk]
        exact hclr0 k hk
      · rw [tlpLift_of_ne _ hk hl]
        have e : WBlk (k.pred hk) (l.pred hl) = W k l := by
          have e' : WBlk (k.pred hk) (l.pred hl) =
              W (k.pred hk).succ (l.pred hl).succ := rfl
          rw [e', Fin.succ_pred, Fin.succ_pred]
        rw [e]
  set lifted : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    Lih.map tlpLift with hlifteddef
  have hliftlen : lifted.length = n * (n - 1) / 2 := by
    rw [hlifteddef, List.length_map]
    exact hlenih
  have hliftval : ∀ M ∈ lifted, M ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
      ∃ (s : ℕ) (hs : s + 1 < n + 1),
        M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ := by
    intro M hM
    rw [hlifteddef, List.mem_map] at hM
    obtain ⟨M0, hM0mem, rfl⟩ := hM
    obtain ⟨hM0u, s, hs, hM02l⟩ := hvalih M0 hM0mem
    refine ⟨tlpLift_mem_unitary M0 hM0u, s + 1, by omega, ?_⟩
    exact tlpLift_isTwoLevel M0 hs hM02l
  have hliftprod : lifted.prod = W := by
    rw [hlifteddef, tlpLift_prod, hprodih]
    exact hblock.symm
  have hall : ∀ G ∈ Gs, G ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    fun G hG => (hval G hG).1
  have h2l : ∀ G ∈ Gs, ∃ (s : ℕ) (hs : s + 1 < n + 1),
      G.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ :=
    fun G hG => (hval G hG).2
  obtain ⟨invGs, hinvlen, hinvmem, hinvprod⟩ := tlp_invGs_prod Gs hall
  have hinvlen' : invGs.length = n := by rw [hinvlen, hlen]
  have hinvval : ∀ M ∈ invGs, M ∈ unitaryGroup (Fin (n + 1)) ℂ ∧
      ∃ (s : ℕ) (hs : s + 1 < n + 1),
        M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩ := by
    intro M hM
    obtain ⟨G, hGmem, hG, rfl⟩ := hinvmem M hM
    obtain ⟨s, hs, hG2l⟩ := h2l G hGmem
    refine ⟨((⟨G, hG⟩ : unitaryGroup (Fin (n + 1)) ℂ)⁻¹).property, s, hs, ?_⟩
    exact tlp_inv_isTwoLevel ⟨G, hG⟩ _ _ hG2l
  have hU : U = invGs.prod * W := by
    calc U = 1 * U := (one_mul U).symm
      _ = (invGs.prod * Gs.reverse.prod) * U := by rw [hinvprod]
      _ = invGs.prod * (Gs.reverse.prod * U) := by rw [mul_assoc]
      _ = invGs.prod * W := by rw [← hW]
  refine ⟨invGs ++ lifted, ?_, ?_, ?_⟩
  · rw [List.length_append, hinvlen', hliftlen, Nat.add_sub_cancel]
    exact tlp_count_add n hn
  · intro M hM
    rw [List.mem_append] at hM
    rcases hM with hM | hM
    · exact hinvval M hM
    · exact hliftval M hM
  · rw [List.prod_append, hliftprod]
    exact hU.symm

private theorem tlp_all (d : ℕ) (hd : 2 ≤ d) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ unitaryGroup (Fin d) ℂ) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      L.length = d * (d - 1) / 2 ∧
      (∀ M ∈ L, M ∈ unitaryGroup (Fin d) ℂ ∧
        ∃ (s : ℕ) (hs : s + 1 < d),
          M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
      L.prod = U := by
  revert U hU
  induction d, hd using Nat.le_induction with
  | base =>
    intro U hU
    exact tlp_base_two U hU
  | succ n hn ih =>
    intro U hU
    exact tlp_step n hn ih U hU

/-- Every unitary of dimension at least two is a product of exactly
`d * (d - 1) / 2` adjacent two-level unitaries. -/
theorem exists_twoLevel_prod_eq {d : ℕ} (hd : 2 ≤ d)
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ unitaryGroup (Fin d) ℂ) :
    ∃ L : List (Matrix (Fin d) (Fin d) ℂ),
      L.length = d * (d - 1) / 2 ∧
      (∀ M ∈ L, M ∈ unitaryGroup (Fin d) ℂ ∧
        ∃ (s : ℕ) (hs : s + 1 < d),
          M.IsTwoLevel ⟨s, by omega⟩ ⟨s + 1, hs⟩) ∧
      L.prod = U := by
  exact tlp_all d hd U hU

/-- Every unitary is a product of at most `d * (d - 1) / 2` two-level
unitaries followed by a diagonal unitary phase matrix. -/
theorem exists_twoLevel_prod_mul_diagonal_eq {d : ℕ}
    {U : Matrix (Fin d) (Fin d) ℂ} (hU : U ∈ unitaryGroup (Fin d) ℂ) :
    ∃ (L : List (Matrix (Fin d) (Fin d) ℂ)) (φ : Fin d → ℂ),
      L.length ≤ d * (d - 1) / 2 ∧
      (∀ M ∈ L, M ∈ unitaryGroup (Fin d) ℂ ∧ ∃ i j, M.IsTwoLevel i j) ∧
      (∀ k, ‖φ k‖ = 1) ∧
      L.prod * diagonal φ = U := by
  by_cases hd : 2 ≤ d
  · obtain ⟨L, hlen, hval, hprod⟩ := exists_twoLevel_prod_eq hd hU
    refine ⟨L, fun _ => 1, by omega, ?_, ?_, ?_⟩
    · intro M hM
      obtain ⟨hu, s, hs, h2l⟩ := hval M hM
      exact ⟨hu, _, _, h2l⟩
    · intro k
      simp
    · rw [hprod]
      simp
  · have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with rfl | rfl
    · refine ⟨[], fun _ => 1, by decide, by simp, ?_, ?_⟩
      · intro k
        have h := k.isLt
        omega
      · simp only [List.prod_nil, one_mul]
        apply Matrix.ext_iff.mp
        intro i j
        have h := i.isLt
        omega
    · refine ⟨[], fun _ => U 0 0, by decide, by simp, ?_, ?_⟩
      · intro k
        have hstar : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
        have h00 := congrArg
          (fun M : Matrix (Fin 1) (Fin 1) ℂ => M 0 0) hstar
        rw [Matrix.mul_apply, Fin.sum_univ_one] at h00
        rw [Matrix.star_apply] at h00
        have hsq := Complex.conj_mul' (U 0 0)
        rw [show star (U 0 0) = (starRingEnd ℂ) (U 0 0) from rfl, hsq,
          Matrix.one_apply_eq] at h00
        have hreal : ‖U 0 0‖ ^ 2 = 1 := by exact_mod_cast h00
        have hpos : 0 ≤ ‖U 0 0‖ := norm_nonneg _
        rcases sq_eq_one_iff.mp hreal with h1 | h1
        · exact h1
        · linarith
      · simp only [List.prod_nil, one_mul]
        apply Matrix.ext_iff.mp
        intro i j
        have hi : i = 0 := Subsingleton.elim i 0
        have hj : j = 0 := Subsingleton.elim j 0
        subst hi
        subst hj
        rw [Matrix.diagonal_apply_eq]

end Matrix
