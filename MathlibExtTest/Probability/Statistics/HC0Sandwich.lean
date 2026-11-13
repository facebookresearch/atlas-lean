/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.HC0Sandwich
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for HC0 sandwich estimator consistency

Entrywise-bound checks, a degenerate satisfiability check, an exact-value
application of `hc0Sandwich_tendsto_ae` for a constant `Fin 1` sandwich case
(bread `1`, meat `5`, sandwich limit `5`), and a constant `Fin 2` case with the
nonsymmetric bread `!![1, 1; 0, 1]` and identity meat: the sandwich limit
`Q⁻¹ * 1 * Q⁻ᵀ = !![2, -1; -1, 1]` is symmetric, while the untransposed
`Q⁻¹ * 1 * Q⁻¹ = !![1, -2; 0, 1]` is not.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.HC0Sandwich

-- Test snippet for ST05.T03 (for MathlibExtTest/Probability/Statistics/HC0Sandwich.lean).
-- In the real test file, the import below replaces the header:
--   import MathlibExt.Probability.Statistics.HC0Sandwich

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.HC0Sandwich
open scoped Matrix

/-- Constant families are independent (for the degenerate satisfiability check). -/
private lemma iIndepFun_const_test {Ω β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace β] (c : β) :
    iIndepFun (fun _ : ℕ => fun _ : Ω => c) μ := by
  simp only [iIndepFun_iff]
  intro s f' H
  have hmem : ∀ i ∈ s, f' i = ∅ ∨ f' i = Set.univ := by
    intro i hi
    have hci := H i hi
    rw [MeasurableSpace.comap_const] at hci
    exact MeasurableSpace.measurableSet_bot_iff.mp hci
  by_cases hall : ∀ i ∈ s, f' i = Set.univ
  · have hinter : ⋂ i ∈ s, f' i = Set.univ :=
      Set.eq_univ_of_forall (fun ω => by
        simp only [Set.mem_iInter]
        intro i hi
        rw [hall i hi]
        trivial)
    have hprod : ∏ i ∈ s, μ (f' i) = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [hall i hi, measure_univ])
    rw [hinter, hprod, measure_univ]
  · push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    have hiempty : f' i = ∅ := by
      rcases hmem i hi with h | h
      · exact h
      · exact absurd h hne
    have hsub : ⋂ i ∈ s, f' i ⊆ f' i := by
      intro ω hω
      simp only [Set.mem_iInter] at hω
      exact hω i hi
    rw [hiempty] at hsub
    have hinter : ⋂ i ∈ s, f' i = ∅ := Set.subset_empty_iff.mp hsub
    have hprod : ∏ i ∈ s, μ (f' i) = 0 :=
      Finset.prod_eq_zero hi (by rw [hiempty]; exact measure_empty)
    rw [hinter, hprod]
    exact measure_empty

/-- Numeric check of the entrywise bound at `ι = Fin 1`, `n = 2`. -/
example : |(hc0Meat (fun _ : ℕ => fun _ : Fin 1 => (1:ℝ))
      (fun i : ℕ => (2 * (i:ℝ) + 3) - (fun _ : Fin 1 => (1:ℝ)) ⬝ᵥ (fun _ : Fin 1 => (2:ℝ))) 2) 0 0
      - (hc0Meat (fun _ : ℕ => fun _ : Fin 1 => (1:ℝ)) (fun i : ℕ => (2 * (i:ℝ) + 3)) 2) 0 0| ≤ 20 := by
  have h := hc0Meat_entrywise_sub_le (x := fun _ : ℕ => fun _ : Fin 1 => (1:ℝ))
    (u := fun i : ℕ => (2 * (i:ℝ) + 3)) (δ := fun _ : Fin 1 => (2:ℝ)) (n := 2) (by norm_num) 0 0
  have hRHS : 2 * (Fintype.card (Fin 1) : ℝ) * ‖(fun _ : Fin 1 => (2:ℝ))‖ *
      ((2 : ℝ)⁻¹ * ∑ i ∈ Finset.range 2, ‖(fun _ : Fin 1 => (1:ℝ))‖ ^ 3 * |2 * (i:ℝ) + 3|) +
      (Fintype.card (Fin 1) : ℝ) ^ 2 * ‖(fun _ : Fin 1 => (2:ℝ))‖ ^ 2 *
      ((2 : ℝ)⁻¹ * ∑ i ∈ Finset.range 2, ‖(fun _ : Fin 1 => (1:ℝ))‖ ^ 4) = 20 := by
    simp [pi_norm_const, Finset.sum_range_succ]
    norm_num
  have h2 : |(hc0Meat (fun _ : ℕ => fun _ : Fin 1 => (1:ℝ))
      (fun i : ℕ => (2 * (i:ℝ) + 3) - (fun _ : Fin 1 => (1:ℝ)) ⬝ᵥ (fun _ : Fin 1 => (2:ℝ))) 2) 0 0
      - (hc0Meat (fun _ : ℕ => fun _ : Fin 1 => (1:ℝ)) (fun i : ℕ => (2 * (i:ℝ) + 3)) 2) 0 0|
      ≤ 2 * (Fintype.card (Fin 1) : ℝ) * ‖(fun _ : Fin 1 => (2:ℝ))‖ *
      ((2 : ℝ)⁻¹ * ∑ i ∈ Finset.range 2, ‖(fun _ : Fin 1 => (1:ℝ))‖ ^ 3 * |2 * (i:ℝ) + 3|) +
      (Fintype.card (Fin 1) : ℝ) ^ 2 * ‖(fun _ : Fin 1 => (2:ℝ))‖ ^ 2 *
      ((2 : ℝ)⁻¹ * ∑ i ∈ Finset.range 2, ‖(fun _ : Fin 1 => (1:ℝ))‖ ^ 4) := h
  rw [hRHS] at h2
  exact h2

/-- Degenerate satisfiability check for the meat consistency hypotheses. -/
example {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (β : ι → ℝ) (a b : ι) :
    ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun n : ℕ => (hc0Meat (fun _ : ℕ => (0 : ι → ℝ))
        (fun _ : ℕ => (0:ℝ) - (0 : ι → ℝ) ⬝ᵥ (β - β)) n) a b)
      Filter.atTop
      (nhds (∫ _, (0:ℝ) ^ 2 * (0 : ι → ℝ) a * (0 : ι → ℝ) b ∂μ)) := by
  have hJ : iIndepFun (fun _ : ℕ => fun _ : Ω => ((0 : ι → ℝ), (0:ℝ))) μ :=
    iIndepFun_const_test _
  have hI : ∀ i : ℕ, IdentDistrib (fun _ : Ω => ((0 : ι → ℝ), (0:ℝ)))
      (fun _ : Ω => ((0 : ι → ℝ), (0:ℝ))) μ μ :=
    fun _ => IdentDistrib.refl aemeasurable_const
  have hM4 : Integrable (fun _ : Ω => ‖(0 : ι → ℝ)‖ ^ 4) μ := by simp
  have hM2 : Integrable (fun _ : Ω => ‖(0 : ι → ℝ)‖ ^ 2 * (0:ℝ) ^ 2) μ := by simp
  have hIM : ∀ a' b' : ι, Integrable
      (fun _ : Ω => (0:ℝ) ^ 2 * (0 : ι → ℝ) a' * (0 : ι → ℝ) b') μ := fun _ _ => by simp
  have hB : ∀ᵐ ω ∂μ, Filter.Tendsto (fun _ : ℕ => β) Filter.atTop (nhds β) :=
    Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have h := hc0Meat_tendsto_ae (x := fun _ _ => (0 : ι → ℝ)) (u := fun _ _ => (0:ℝ))
    (β := β) (βhat := fun _ _ => β) hJ hI hM4 hM2 hIM hB a b
  exact h

/-- Exact-value check: a constant `Fin 1` sandwich converges to the stated
`Q⁻¹ * Ωm * Q⁻ᵀ` value (here bread `Q = 1`, meat `Ωm = 5`, limit `5`). -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (a b : Fin 1) :
    ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => (((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
        * Matrix.of (fun _ _ : Fin 1 => (5:ℝ))
        * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)ᵀ)) a b)
      Filter.atTop (nhds 5) := by
  have hQinv : ∀ a' b' : Fin 1, ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => (((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)) a' b')
      Filter.atTop (nhds ((((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)) a' b')) :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have hMeat : ∀ a' b' : Fin 1, ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => Matrix.of (fun _ _ : Fin 1 => (5:ℝ)) a' b')
      Filter.atTop (nhds (Matrix.of (fun _ _ : Fin 1 => (5:ℝ)) a' b')) :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have h := hc0Sandwich_tendsto_ae (Qhat := fun _ _ => (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (Q := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (Ωm := Matrix.of (fun _ _ : Fin 1 => (5:ℝ)))
    (meat := fun _ _ => Matrix.of (fun _ _ : Fin 1 => (5:ℝ))) hQinv hMeat a b
  have hval : ((((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹
      * Matrix.of (fun _ _ : Fin 1 => (5:ℝ))
      * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹)ᵀ)) a b) = 5 := by
    simp only [inv_one, Matrix.transpose_one, one_mul, mul_one, Matrix.of_apply]
  rw [hval] at h ⊢
  exact h

/-- The nonsymmetric bread `!![1, 1; 0, 1]` has inverse `!![1, -1; 0, 1]`. -/
private lemma bread_fin_two_inv :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1, -1; 0, 1] := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- With the nonsymmetric bread `!![1, 1; 0, 1]` and identity meat, the covariance
sandwich `Q⁻¹ * 1 * Q⁻ᵀ` is the symmetric `!![2, -1; -1, 1]`. -/
private lemma sandwich_fin_two :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹)ᵀ = !![2, -1; -1, 1] := by
  rw [bread_fin_two_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Without the transpose, the same data give the nonsymmetric `!![1, -2; 0, 1]`. -/
private lemma untransposed_fin_two :
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![1, -2; 0, 1] := by
  rw [bread_fin_two_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- Nonsymmetric `Fin 2` check: for the constant bread `Q = !![1, 1; 0, 1]` and identity
meat, every entry of the sandwich converges to the symmetric limit
`Q⁻¹ * 1 * Q⁻ᵀ = !![2, -1; -1, 1]`. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (a b : Fin 2) :
    ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) a b)
      Filter.atTop (nhds ((!![2, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) a b)) := by
  have hQinv : ∀ a' b' : Fin 2, ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹) a' b')
      Filter.atTop (nhds (((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹) a' b')) :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  have hMeat : ∀ a' b' : Fin 2, ∀ᵐ _ ∂μ, Filter.Tendsto
      (fun _ : ℕ => (1 : Matrix (Fin 2) (Fin 2) ℝ) a' b')
      Filter.atTop (nhds ((1 : Matrix (Fin 2) (Fin 2) ℝ) a' b')) :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => tendsto_const_nhds)
  rw [← sandwich_fin_two]
  exact hc0Sandwich_tendsto_ae
    (Qhat := fun _ _ => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (Q := !![1, 1; 0, 1]) (Ωm := 1) (meat := fun _ _ => 1) hQinv hMeat a b

/-- The sandwich limit for that bread is symmetric (equal off-diagonal entries), while the
untransposed `Q⁻¹ * 1 * Q⁻¹` is not, so the two forms differ. -/
example :
    ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹)ᵀ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ∧
    ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠
      ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ * 1 *
        (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
  rw [sandwich_fin_two, untransposed_fin_two]
  norm_num

end MathlibExtTest.Probability.Statistics.HC0Sandwich
