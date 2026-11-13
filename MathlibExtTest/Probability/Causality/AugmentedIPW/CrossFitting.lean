/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

/-!
# Tests for cross-fitted AIPW

Fold bookkeeping on a concrete assignment, the cross-fitted estimator computed from its
definition (including a fitted score that reads the training data), the perfect-nuisance
boundary, a both-wrong fixture where the remainder is nonzero and the product bound is attained,
and the failure of the variance identity for an uncentered kernel.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

namespace MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting

/-- Alternating two-fold assignment, independent of the sample size. -/
def parity : ℕ → ℕ → Fin 2 := fun _ i => ⟨i % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Fold `0` at sample size `4` evaluates the even units and trains on the odd ones. -/
example : evalFold parity 4 0 = {0, 2} ∧ trainFold parity 4 0 = {1, 3} := by
  decide

/-- Boundary: at sample size `0` every fold is empty. -/
example (k : Fin 2) : evalFold parity 0 k = ∅ ∧ trainFold parity 0 k = ∅ := by
  simp [evalFold, trainFold]

/-- For any fold assignment, evaluation and training indices of a fold partition `range n`:
no unit is scored with nuisances fitted on itself. -/
example {K : ℕ} (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) :
    Disjoint (evalFold fold n k) (trainFold fold n k) ∧
      evalFold fold n k ∪ trainFold fold n k = Finset.range n :=
  ⟨Finset.disjoint_filter_filter_not _ _ _, Finset.filter_union_filter_not_eq _ _⟩

/-- A fitted score that ignores the training data: the estimator is the sample mean. With
`W i = i`, at `n = 2` it is `(0 + 1) / 2`. -/
example : crossFitEstimator (fun i (_ : Unit) => (i : ℝ)) parity (fun _ _ z => z.2) 2 () =
    1 / 2 := by
  simp [crossFitEstimator, Finset.sum_range_succ]

/-- A fitted score that reads only the training data (the sum of the training observations).
With `W i = i + 1` and `n = 2`, unit `0` (fold `0`) is scored on the training set `{1}` and unit
`1` (fold `1`) on `{0}`, so the estimator is `(W 1 + W 0) / 2 = 3 / 2`: each unit's own
observation is excluded from its nuisance. -/
example : crossFitEstimator (fun i (_ : Unit) => (i : ℝ) + 1) parity
    (fun n k z => ∑ j : trainFold parity n k, z.1 j) 2 () = 3 / 2 := by
  have h0 : trainFold parity 2 0 = {1} := by decide
  have h1 : trainFold parity 2 1 = {0} := by decide
  have hsum : ∀ k : Fin 2, ∑ j : trainFold parity 2 k, trainData (fun i (_ : Unit) => (i : ℝ) + 1)
      parity 2 k () j = ∑ j ∈ trainFold parity 2 k, ((j : ℝ) + 1) := fun k =>
    Finset.sum_coe_sort (trainFold parity 2 k) (fun j => (j : ℝ) + 1)
  simp only [crossFitEstimator, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hp0 : parity 2 0 = 0 := rfl
  have hp1 : parity 2 1 = 1 := rfl
  rw [hp0, hp1, hsum 0, hsum 1, h0, h1]
  norm_num

/-- Perfect-nuisance boundary: if every fitted score equals the oracle score `ψ`, the
cross-fitted estimator is the oracle estimator `n⁻¹ ∑ ψ(W i)`, so the oracle gap is `0`. -/
example {Ω 𝒲 : Type*} [MeasurableSpace 𝒲] {K : ℕ} (W : ℕ → Ω → 𝒲) (fold : ℕ → ℕ → Fin K)
    (ψ : 𝒲 → ℝ) (n : ℕ) (ω : Ω) :
    crossFitEstimator W fold (fun _ _ z => ψ z.2) n ω =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (W i ω) :=
  rfl

/-- On a one-point space with the full σ-algebra, conditional expectations are the functions
themselves. -/
private lemma condExp_unit (f : Unit → ℝ) :
    (Measure.dirac ())[f | (inferInstance : MeasurableSpace Unit)] = f :=
  condExp_of_stronglyMeasurable le_rfl (measurable_of_countable f).stronglyMeasurable
    (Integrable.of_finite (μ := Measure.dirac ()))

/-- Both-wrong fixture, computed from the definition of `aipwRemainder`: everyone treated
(`e* = 1`), `Y₁ = 2`, `Y₀ = 0`, candidates `e = 1/2`, `g₁ = 0`, `g₀ = 0`. The remainder is
`(1 - 1/2) · (2 / (1/2)) = 2 ≠ 0`: with neither nuisance correct the bias is nonzero. -/
example : aipwRemainder (Measure.dirac ()) (inferInstance : MeasurableSpace Unit) Set.univ
    (fun _ => 0) (fun _ => 2) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0) = 2 := by
  simp only [aipwRemainder, condExp_unit, integral_dirac, Set.indicator_univ, Pi.one_apply]
  norm_num

/-- The product bound of `abs_aipwRemainder_le` is attained on the both-wrong fixture: with
`ε = 1/2`, `ε⁻¹ ‖e* - e‖₂ (‖μ₁* - g₁‖₂ + ‖μ₀* - g₀‖₂) = 2 · (1/2) · (2 + 0) = 2`, the value of the
remainder computed above. -/
example : (1 / 2 : ℝ)⁻¹ * √(∫ ω, ((fun _ : Unit => (1 : ℝ)) ω - 1 / 2) ^ 2 ∂Measure.dirac ()) *
    (√(∫ ω, ((fun _ : Unit => (2 : ℝ)) ω - 0) ^ 2 ∂Measure.dirac ()) +
      √(∫ ω, ((fun _ : Unit => (0 : ℝ)) ω - 0) ^ 2 ∂Measure.dirac ())) = 2 := by
  simp only [integral_dirac]
  have h1 : √((1 - 1 / 2 : ℝ) ^ 2) = 1 / 2 := by
    rw [Real.sqrt_sq (by norm_num)]; norm_num
  have h2 : √((2 - 0 : ℝ) ^ 2) = 2 := by
    rw [Real.sqrt_sq (by norm_num)]; norm_num
  rw [h1, h2]
  norm_num

/-- Centering is needed in the variance identity: for the uncentered kernel `D ≡ 1` and two
evaluation units, `(∑ D)² = 4`, not `|s| · D² = 2`. -/
example : (∑ _i ∈ Finset.range 2, (1 : ℝ)) ^ 2 ≠ (Finset.range 2).card * 1 ^ 2 := by
  norm_num

end MathlibExtTest.Probability.Causality.AugmentedIPW.CrossFitting
