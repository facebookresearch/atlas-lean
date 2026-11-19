/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Statistics.CalibrationPorts

/-!
# Tests for `PhyslibExt.Statistics.CalibrationPorts`

* a gauge with zero gain is not identifiable;
* the signed weights `(2, -1)` sum to one but give a negative strain "variance", so the
  nonnegativity of the weights is part of the physical model;
* voltages `7.5 mV` and `12.5 mV` with equal weights, offset `10 mV` and gain `2.5 V` give the
  strains `∓0.001` with variance `10⁻⁶`;
* two perfectly correlated gauges averaged with weights `1/2` have strain variance `10⁻⁶`, while
  adding their variances as if independent gives the wrong value `5 · 10⁻⁷`.
-/

@[expose] public section

namespace PhyslibExtTest.Statistics.CalibrationPorts

open Matrix MathlibExt.Probability.FiniteProbability Statistics.UncertaintyPropagation
  _root_.Statistics.CalibrationPorts

/-! ## A. A zero gain -/

/-- A zero gain loses identifiability: a gauge with `g = 0` reports the same voltage for every
strain. -/
example : ¬ Identifiable (diagonal ![(0 : ℝ)]) := by
  rw [identifiable_diagonal_iff]
  intro h
  exact h 0 rfl

/-! ## B. Signed weights -/

/-- **Signed weights are not a probability model**: the weights `(2, -1)` sum to one, so the
algebraic propagation identities apply, but the strain of the voltages `(0, 1)` with unit gain
and zero offset then has the negative "variance" `-2`. -/
example :
    ∑ ω, ![(2 : ℝ), -1] ω = 1 ∧
      variance ![2, -1] (fun ω => gaugeStrain 1 0 (![(0 : ℝ), 1] ω) one_ne_zero) = -2 := by
  constructor
  · simp [Fin.sum_univ_two]
    norm_num
  · simp [variance, expectation, Fin.sum_univ_two, gaugeStrain]
    norm_num

/-! ## C. Nonzero uncertainty and correlated channels -/

/-- Nonzero voltage uncertainty and gain: the equal weights `1/2, 1/2` are a finite
distribution, and voltages `3/400` and `1/80` (7.5 mV and 12.5 mV) with offset `1/100` and gain
`5/2` give the strains `∓1/1000` with variance `10⁻⁶`; the voltage variance is `(1/400)²`. -/
example :
    (∀ ω, 0 ≤ ![(1 : ℝ) / 2, 1 / 2] ω) ∧ ∑ ω, ![(1 : ℝ) / 2, 1 / 2] ω = 1 ∧
      variance ![1 / 2, 1 / 2] ![(3 : ℝ) / 400, 1 / 80] = 1 / 160000 ∧
      variance ![1 / 2, 1 / 2]
          (fun ω => gaugeStrain (5 / 2) (1 / 100) (![3 / 400, 1 / 80] ω) (by norm_num)) =
        1 / 1000000 := by
  refine ⟨fun ω => ?_, ?_, ?_, ?_⟩
  · fin_cases ω <;> norm_num
  · simp [Fin.sum_univ_two]
    norm_num
  · simp [variance, expectation, Fin.sum_univ_two]
    norm_num
  · simp [variance, expectation, Fin.sum_univ_two, gaugeStrain]
    norm_num

/-- Correlated channels cannot be combined as independent variances: two gauges with identical
voltages averaged with weights `1/2` have strain variance `10⁻⁶`, while adding their variances as
if independent gives `5 · 10⁻⁷`. -/
example :
    covMatrix ![1 / 2, 1 / 2]
        (fun ω => Matrix.of ![![1 / 2, 1 / 2]] *ᵥ
          gaugeStrainVec ![5 / 2, 5 / 2] ![1 / 100, 1 / 100]
            (![![(3 : ℝ) / 400, 3 / 400], ![1 / 80, 1 / 80]] ω)
            (by intro i; fin_cases i <;> norm_num)) 0 0 = 1 / 1000000 ∧
      (1 / 2) ^ 2 * covMatrix ![1 / 2, 1 / 2]
          (fun ω => gaugeStrainVec ![5 / 2, 5 / 2] ![1 / 100, 1 / 100]
            (![![(3 : ℝ) / 400, 3 / 400], ![1 / 80, 1 / 80]] ω)
            (by intro i; fin_cases i <;> norm_num)) 0 0 +
        (1 / 2) ^ 2 * covMatrix ![1 / 2, 1 / 2]
          (fun ω => gaugeStrainVec ![5 / 2, 5 / 2] ![1 / 100, 1 / 100]
            (![![(3 : ℝ) / 400, 3 / 400], ![1 / 80, 1 / 80]] ω)
            (by intro i; fin_cases i <;> norm_num)) 1 1 = 1 / 2000000 := by
  constructor <;>
    simp [covMatrix, covariance, expectation, Fin.sum_univ_two, gaugeStrainVec, gaugeStrain,
      Matrix.mulVec, dotProduct] <;> norm_num

end PhyslibExtTest.Statistics.CalibrationPorts
