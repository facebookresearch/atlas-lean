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
  adding their variances as if independent gives the wrong value `5 · 10⁻⁷`;
* quadratic calibration: the derivative and the exact remainder at concrete values, the typed
  calibration and its change of units, the Hessian bound and the attained pointwise remainder
  bound, the failure of a global Lipschitz bound, a law with zero linearized variance, the
  rejection of a scenario outside the box, the cross term `21/4` that separates `171/16` from
  `87/16`, a zero-probability scenario that leaves the output variance unchanged, the weights of a
  probability mass function as a scenario law, and the measure-theoretic split.
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

/-! ## D. Quadratic calibration -/

open Dimension Units.QuantityDimensions

/-- The derivative of `f v = 1 + 2 v + v ^ 2` at `v = 1` is `4`, and at the base `0` the value
`f 2 = 9` is the first-order part `5` plus the remainder `4`. -/
example :
    HasDerivAt (quadCalibration 1 2 1) 4 1 ∧ quadCalibration 1 2 1 2 = 9 ∧
      quadLinearPart 1 2 1 0 2 = 5 ∧ quadRemainder 1 0 2 = 4 := by
  have hsplit := quadCalibration_eq_linear_add_remainder 1 2 1 0 2
  have hL : quadLinearPart 1 2 1 0 2 = 5 := by
    simp only [quadLinearPart, quadCalibration]
    norm_num
  have hR : quadRemainder 1 0 2 = 4 := by
    simp only [quadRemainder]
    norm_num
  refine ⟨?_, ?_, hL, hR⟩
  · convert quadCalibration_hasDerivAt 1 2 1 1 using 1
    norm_num
  · rw [hsplit, hL, hR]
    norm_num

/-- With output dimension one, the coefficients `0`, `2`, `1` in their typed dimensions and the
voltage `1` give the typed output coordinate `3`; a change of units leaves a dimension-one output
coordinate unchanged. -/
example (u1 u2 : UnitScale ISQDimensionBase) (c0 c1 c2 v : ℝ) :
    (quadCalibrationQty (d := dimensionlessDim) ⟨0⟩ ⟨2⟩ ⟨1⟩ ⟨1⟩).val = 3 ∧
      quadCalibration ((u1.dimScale u2 dimensionlessDim : ℝ) * c0)
          ((u1.dimScale u2 (dimensionlessDim * voltageDim⁻¹) : ℝ) * c1)
          ((u1.dimScale u2 (dimensionlessDim * (voltageDim⁻¹ * voltageDim⁻¹)) : ℝ) * c2)
          ((u1.dimScale u2 voltageDim : ℝ) * v) =
        quadCalibration c0 c1 c2 v := by
  refine ⟨?_, ?_⟩
  · rw [quadCalibrationQty_val]
    simp only [quadCalibration]
    norm_num
  · rw [quadCalibration_coord_dimScale]
    simp [dimensionlessDim]

/-- The Hessian bound is `2 |c2|`; from the base `0` to the voltage `2` in the box `[0, 2]` the
remainder of `f v = 1 + 2 v + v ^ 2` is exactly `4`, so the pointwise bound `|c2| ‖δ‖ ^ 2 = 4` of
the Hessian theorem is attained. The raw quadratic is not Lipschitz with constant `10`. -/
example :
    ‖fderiv ℝ (fderiv ℝ (fun y => quadCalibrationVec 1 2 1 y 0)) 0‖ ≤ 2 ∧
      jacobianRemainder (quadCalibrationVec 1 2 1) (fun _ => 0) (fun _ => 2) 0 = 4 ∧
      |jacobianRemainder (quadCalibrationVec 1 2 1) (fun _ => 0) (fun _ => 2) 0| ≤ 4 ∧
      ¬ LipschitzWith 10 (quadCalibration 1 2 1) := by
  have hbound := quadCalibrationVec_remainder_le (a := 0) (b := 2) (c0 := 1) (c1 := 2) (c2 := 1)
    (x := fun _ => 0) (δ := fun _ => 2) ⟨le_rfl, fun _ => by norm_num⟩
    ⟨fun _ => by simp, fun _ => by simp⟩
  have hn : ‖(fun _ : Fin 1 => (2 : ℝ))‖ = 2 := by
    rw [pi_norm_const]
    norm_num
  rw [hn] at hbound
  refine ⟨?_, ?_, ?_, quadCalibration_not_lipschitzWith one_ne_zero 10⟩
  · simpa using quadCalibrationVec_hessian_le 1 2 1 0
  · rw [quadCalibrationVec_jacobianRemainder]
    simp only [quadRemainder]
    norm_num
  · norm_num at hbound
    exact hbound

/-- Zero linearized variance: the voltages `(-1, 0, 1)` with weights `(1/4, 1/2, 1/4)` form a
scenario law in `[-1, 1]`; for `f v = v ^ 2` with base `0` the output variance is `1/4`, while
the first-order part has variance `0`. -/
example :
    ScenarioLawIn (-1) 1 ![1 / 4, 1 / 2, 1 / 4] ![-1, 0, 1] ∧
      variance ![1 / 4, 1 / 2, 1 / 4] (fun ω => quadCalibration 0 0 1 (![-1, 0, 1] ω)) =
        1 / 4 ∧
      variance ![1 / 4, 1 / 2, 1 / 4] (fun ω => quadLinearPart 0 0 1 0 (![-1, 0, 1] ω)) = 0 := by
  have hp1 : ∑ ω, ![(1 : ℝ) / 4, 1 / 2, 1 / 4] ω = 1 := by
    simp [Fin.sum_univ_three]
    norm_num
  refine ⟨⟨fun ω => ?_, hp1, fun ω => ?_⟩, ?_, ?_⟩
  · fin_cases ω <;> norm_num
  · fin_cases ω <;> norm_num
  · rw [variance_quadCalibration_expansion _ _ 0 0 1 0, variance_quadLinearPart hp1,
      covariance_quadLinearPart_quadRemainder hp1]
    simp [variance, expectation, Fin.sum_univ_three, quadRemainder]
    norm_num
  · rw [variance_quadLinearPart hp1]
    norm_num

/-- A scenario outside the calibration box is rejected: the voltage `3` is not in `[0, 2]`, so
the voltages `(1, 3)` with weights `(1/2, 1/2)` are not a scenario law in that box. -/
example :
    ¬ ScenarioLawIn 0 2 ![1 / 2, 1 / 2] ![1, 3] := by
  rintro ⟨-, -, hV⟩
  have h := (hV 1).2
  norm_num at h

/-- Nonzero cross covariance: the voltages `(0, 1, 2)` with weights `(1/2, 1/4, 1/4)` form a
scenario law in `[0, 2]`; for `f v = 1 + 2 v + v ^ 2` with base `0` the output variance is
`171/16`, the variances of the first-order part and of the remainder add up to `87/16` only,
and twice their covariance is the missing `21/4`. -/
example :
    ScenarioLawIn 0 2 ![1 / 2, 1 / 4, 1 / 4] ![0, 1, 2] ∧
      variance ![1 / 2, 1 / 4, 1 / 4] (fun ω => quadCalibration 1 2 1 (![0, 1, 2] ω)) =
        171 / 16 ∧
      variance ![1 / 2, 1 / 4, 1 / 4] (fun ω => quadLinearPart 1 2 1 0 (![0, 1, 2] ω)) +
          variance ![1 / 2, 1 / 4, 1 / 4] (fun ω => quadRemainder 1 0 (![0, 1, 2] ω)) =
        87 / 16 ∧
      2 * covariance ![1 / 2, 1 / 4, 1 / 4] (fun ω => quadLinearPart 1 2 1 0 (![0, 1, 2] ω))
          (fun ω => quadRemainder 1 0 (![0, 1, 2] ω)) = 21 / 4 := by
  have hp1 : ∑ ω, ![(1 : ℝ) / 2, 1 / 4, 1 / 4] ω = 1 := by
    simp [Fin.sum_univ_three]
    norm_num
  have hlaw : ScenarioLawIn 0 2 ![1 / 2, 1 / 4, 1 / 4] ![0, 1, 2] := by
    refine ⟨fun ω => ?_, hp1, fun ω => ?_⟩
    · fin_cases ω <;> norm_num
    · fin_cases ω <;> norm_num
  have hV : variance ![(1 : ℝ) / 2, 1 / 4, 1 / 4] ![0, 1, 2] = 11 / 16 := by
    simp [variance, expectation, Fin.sum_univ_three]
    norm_num
  have hV2 : variance ![(1 : ℝ) / 2, 1 / 4, 1 / 4] (fun ω => (![(0 : ℝ), 1, 2] ω - 0) ^ 2) =
      43 / 16 := by
    simp [variance, expectation, Fin.sum_univ_three]
    norm_num
  have hC : covariance ![(1 : ℝ) / 2, 1 / 4, 1 / 4] ![0, 1, 2]
      (fun ω => (![(0 : ℝ), 1, 2] ω - 0) ^ 2) = 21 / 16 := by
    simp [covariance, expectation, Fin.sum_univ_three]
    norm_num
  have hR : variance ![(1 : ℝ) / 2, 1 / 4, 1 / 4] (fun ω => quadRemainder 1 0 (![0, 1, 2] ω)) =
      43 / 16 := by
    simp [variance, expectation, Fin.sum_univ_three, quadRemainder]
    norm_num
  refine ⟨hlaw, ?_, ?_, ?_⟩
  · rw [(variance_quadCalibration_of_scenarioLaw hlaw ⟨le_rfl, by norm_num⟩ 1 2 1).1, hV, hV2,
      hC]
    norm_num
  · rw [variance_quadLinearPart hp1, hV, hR]
    norm_num
  · rw [covariance_quadLinearPart_quadRemainder hp1, hC]
    norm_num

/-- A zero-probability scenario is allowed: the voltages `(0, 2, 1)` with weights `(1/2, 1/2, 0)`
form a scenario law in `[0, 2]`. For `f v = v ^ 2` with base `1` the output variance is `4`, the
same as for the two scenarios of positive weight alone. -/
example :
    ScenarioLawIn 0 2 ![1 / 2, 1 / 2, 0] ![0, 2, 1] ∧
      variance ![1 / 2, 1 / 2, 0] (fun ω => quadCalibration 0 0 1 (![0, 2, 1] ω)) = 4 ∧
      variance ![1 / 2, 1 / 2] (fun ω => quadCalibration 0 0 1 (![0, 2] ω)) = 4 := by
  have hp1 : ∑ ω, ![(1 : ℝ) / 2, 1 / 2, 0] ω = 1 := by
    simp [Fin.sum_univ_three]
    norm_num
  have hlaw : ScenarioLawIn 0 2 ![1 / 2, 1 / 2, 0] ![0, 2, 1] := by
    refine ⟨fun ω => ?_, hp1, fun ω => ?_⟩
    · fin_cases ω <;> norm_num
    · fin_cases ω <;> norm_num
  refine ⟨hlaw, ?_, ?_⟩
  · rw [(variance_quadCalibration_of_scenarioLaw hlaw (v₀ := 1) ⟨by norm_num, by norm_num⟩
      0 0 1).1]
    simp [variance, covariance, expectation, Fin.sum_univ_three]
    norm_num
  · simp [variance, expectation, Fin.sum_univ_two, quadCalibration]
    norm_num

/-- The weights of a probability mass function, which may vanish, form a scenario law with any
voltages in the box. -/
example (q : PMF (Fin 3)) : ScenarioLawIn 0 2 (fun ω => (q ω).toReal) ![0, 1, 2] := by
  obtain ⟨h0, h1⟩ := toReal_weights_isDistribution q
  exact ⟨h0, h1, fun ω => by fin_cases ω <;> norm_num⟩

/-- The measure-theoretic split for a probability mass function on the three voltages `0, 1, 2`:
the output variance keeps twice the cross covariance of the first-order part and the remainder. -/
example (q : PMF (Fin 3)) :
    ProbabilityTheory.variance (fun ω => quadCalibration 1 2 1 (![0, 1, 2] ω)) q.toMeasure =
      ProbabilityTheory.variance (fun ω => quadLinearPart 1 2 1 0 (![0, 1, 2] ω)) q.toMeasure +
        2 * ProbabilityTheory.covariance (fun ω => quadLinearPart 1 2 1 0 (![0, 1, 2] ω))
          (fun ω => quadRemainder 1 0 (![0, 1, 2] ω)) q.toMeasure +
        ProbabilityTheory.variance (fun ω => quadRemainder 1 0 (![0, 1, 2] ω)) q.toMeasure :=
  variance_quadCalibration_toMeasure q _ 1 2 1 0

end PhyslibExtTest.Statistics.CalibrationPorts
