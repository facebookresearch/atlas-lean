/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Statistics.DesignSensitivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for `PhyslibExt.Statistics.DesignSensitivity`

Consistent units (for example kN and m): a bar with axial rigidity `EA = 4` and length `L = 2`
under the end force `F = 2`, and the feasible stiffness interval `[1, 4]`.

* the bar is a spring of stiffness `k = 2`, interior to `[1, 4]`, with tip displacement `1`,
  adjoint `1`, compliance `2` and `dJ/dk = -1`; every zero-load solution has that tip
  displacement;
* at the lower endpoint `k = 1` the feasible directions are `d ≥ 0` and `dJ/dk = -4` within the
  interval; at the upper endpoint `k = 4` they are `d ≤ 0` and `dJ/dk = -1/4`; a degenerate
  interval admits only `d = 0`;
* the singularity at `k = 0` and the absence of an unconstrained minimizer;
* units: `J = F * (F / k)` has the energy dimension;
* error composition: the design `F = 2`, `k = 2` against the estimate `Fhat = 3/2`, `khat = 3`
  with `Fmax = 2`, `kmin = 2`, the intermediate compliance `9/8`, the composed bound `2`, and the
  composition with a supplied model term;
* residuals: with `kmin = 1` the trial `u = 3/2` at `k = 2`, `F = 2` has residual `1`, state error
  `1/2` and compliance error `1`; without a lower stiffness bound, no constant turns the residual
  into a bound on the compliance error for the nonzero force `F = 2`, nor into a bound on the
  state error even for `F = 0`, where the compliance error vanishes and the constant `0` bounds it.
-/

@[expose] public section

namespace PhyslibExtTest.Statistics.DesignSensitivity

open _root_.Statistics.DesignSensitivity _root_.Elasticity.PrismaticMembers

/-- Nonzero force at an interior design: the bar `EA = 4`, `L = 2` under `F = 2` has stiffness
`k = 2`, interior to the feasible interval `[1, 4]` (every direction is feasible there); its
solution `u x = 2 x / 4` has tip displacement `1`, the adjoint is `1`, and `dJ/dk = -1`. -/
lemma tipForce_fixture :
    axialStiffness 4 2 = 2 ∧ axialStiffness 4 2 ∈ Set.Ioo 1 4 ∧
      feasibleDirections 1 4 (axialStiffness 4 2) = Set.univ ∧
      IsFixedTractionSolution 4 2 2 (fun _ => 0) (fun x => 2 * x / 4) ∧
      tipDisplacement 2 (axialStiffness 4 2) = 1 ∧
      adjointDisplacement 2 (axialStiffness 4 2) = 1 ∧
      HasDerivAt (compliance 2) (-1) (axialStiffness 4 2) := by
  have h42 : axialStiffness 4 2 = 2 := by unfold axialStiffness; norm_num
  rw [h42]
  refine ⟨rfl, ⟨by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact feasibleDirections_interior ⟨by norm_num, by norm_num⟩
  · exact isFixedTractionSolution_zero_load (by norm_num) (by norm_num)
  · unfold tipDisplacement; norm_num
  · unfold adjointDisplacement; norm_num
  · have h := hasDerivAt_compliance (show (0 : ℝ) < 2 by norm_num) 2
    rw [show adjointDisplacement 2 2 = 1 from by unfold adjointDisplacement; norm_num,
      show tipDisplacement 2 2 = 1 from by unfold tipDisplacement; norm_num] at h
    norm_num at h
    exact h

/-- The singularity at `k = 0` is excluded: the formulas take the division-by-zero values
`J 0 = 0` and `-F² / 0² = 0`, but for `F ≠ 0` the compliance is not differentiable at `0`. -/
lemma compliance_zero_singularity {F : ℝ} (hF : F ≠ 0) :
    compliance F 0 = 0 ∧ -F ^ 2 / (0 : ℝ) ^ 2 = 0 ∧ ¬ DifferentiableAt ℝ (compliance F) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold compliance tipDisplacement; simp
  · simp
  · intro hdiff
    have hcont := hdiff.continuousAt
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont 1 zero_lt_one
    have hF2 : 0 < F ^ 2 := by positivity
    set k0 := min (δ / 2) (F ^ 2 / 2) with hk0def
    have hk0pos : 0 < k0 := lt_min (by linarith) (by linarith)
    have hk0ne : k0 ≠ 0 := ne_of_gt hk0pos
    have hk0δ : dist k0 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hk0pos]
      have h1 : k0 ≤ δ / 2 := min_le_left _ _
      linarith
    have hcon := hball hk0δ
    have hJ0 : compliance F 0 = 0 := by unfold compliance tipDisplacement; simp
    have hJk0 : compliance F k0 = F ^ 2 / k0 := by
      unfold compliance tipDisplacement
      field_simp
    have hdist : dist (compliance F k0) (compliance F 0) = F ^ 2 / k0 := by
      rw [Real.dist_eq, hJ0, hJk0, sub_zero]
      exact abs_of_nonneg (by positivity)
    have hk0le : k0 ≤ F ^ 2 / 2 := min_le_right _ _
    have hge : 2 ≤ F ^ 2 / k0 := by
      rw [le_div_iff₀ hk0pos]
      linarith
    rw [hdist] at hcon
    linarith

/-- No unconstrained optimum: for `F ≠ 0` the compliance has no minimizer on `k > 0`. -/
lemma not_exists_isMinOn_compliance {F : ℝ} (hF : F ≠ 0) :
    ¬ ∃ k ∈ Set.Ioi (0 : ℝ), IsMinOn (compliance F) (Set.Ioi 0) k := by
  rintro ⟨k, hk, hmin⟩
  have hkpos : (0 : ℝ) < k := hk
  have hk1pos : (0 : ℝ) < k + 1 := by linarith
  have hk1mem : k + 1 ∈ Set.Ioi (0 : ℝ) := hk1pos
  have hle : compliance F k ≤ compliance F (k + 1) := hmin hk1mem
  have hF2 : 0 < F ^ 2 := by positivity
  have hlt : compliance F (k + 1) < compliance F k := by
    have e1 : compliance F (k + 1) = F ^ 2 / (k + 1) := by
      unfold compliance tipDisplacement
      have hk1ne : k + 1 ≠ 0 := ne_of_gt hk1pos
      field_simp
    have e2 : compliance F k = F ^ 2 / k := by
      unfold compliance tipDisplacement
      have hkne : k ≠ 0 := ne_of_gt hkpos
      field_simp
    rw [e1, e2]
    exact div_lt_div_of_pos_left hF2 hkpos (by linarith)
  linarith

-- Every zero-load solution of the bar `EA = 4`, `L = 2` under `F = 2` has tip displacement `1`;
-- its load work is the compliance `2` of the positive stiffness `k = 2`.
example {u : ℝ → ℝ} (hu : IsFixedTractionSolution 4 2 2 (fun _ => 0) u) :
    0 < axialStiffness 4 2 ∧ u 2 = 1 ∧ 2 * u 2 = compliance 2 (axialStiffness 4 2) ∧
      compliance 2 (axialStiffness 4 2) = 2 := by
  obtain ⟨htip, hwork⟩ := tip_eq_of_isFixedTractionSolution (by norm_num) (by norm_num) hu
  have hk : axialStiffness 4 2 = 2 := by norm_num [axialStiffness]
  refine ⟨axialStiffness_pos (by norm_num) (by norm_num), ?_, hwork, ?_⟩
  · rw [htip, hk]
    norm_num [tipDisplacement]
  · rw [hk]
    norm_num [compliance, tipDisplacement]

-- The adjoint of `F = 2` at `k = 2` solves `k * p = F`, and `dJ/dk = -p * u_tip = -1 ≠ 0`.
example : 2 * adjointDisplacement 2 2 = 2 ∧ deriv (compliance 2) 2 = -1 ∧
    deriv (compliance 2) 2 ≠ 0 := by
  refine ⟨stiffness_mul_adjointDisplacement (by norm_num) 2, ?_,
    deriv_compliance_ne_zero (by norm_num) (by norm_num)⟩
  rw [(hasDerivAt_compliance (by norm_num : (0 : ℝ) < 2) 2).deriv,
    neg_adjointDisplacement_mul_tipDisplacement]
  norm_num

-- At the lower endpoint `k = 1` of `[1, 4]` the feasible directions are `d ≥ 0`, and the
-- compliance of `F = 2` has the derivative `-4` within the interval.
example : feasibleDirections 1 4 1 = Set.Ici 0 ∧
    HasDerivWithinAt (compliance 2) (-4) (Set.Icc 1 4) 1 := by
  refine ⟨feasibleDirections_left (by norm_num), ?_⟩
  have h := hasDerivWithinAt_compliance_Icc (kmin := 1) (kmax := 4) (k := 1) one_pos
    ⟨le_rfl, by norm_num⟩ 2
  convert h using 1
  norm_num

-- At the upper endpoint `k = 4` the derivative within `[1, 4]` is `-1/4 < 0`, so the endpoint is
-- not stationary; `d = -1` is a feasible direction there and `d = 1` is not.
example : HasDerivWithinAt (compliance 2) (-1 / 4) (Set.Icc 1 4) 4 ∧
    (-1 : ℝ) ∈ feasibleDirections 1 4 4 ∧ (1 : ℝ) ∉ feasibleDirections 1 4 4 := by
  obtain ⟨h, -, -⟩ := compliance_upper_endpoint (F := 2) (kmin := 1) (kmax := 4)
    (by norm_num) one_pos (by norm_num)
  rw [feasibleDirections_right (by norm_num : (1 : ℝ) < 4)]
  refine ⟨?_, by norm_num, by norm_num⟩
  convert h using 1
  norm_num

-- A degenerate interval `[2, 2]` admits only the zero direction.
example : feasibleDirections 2 2 2 = {0} :=
  feasibleDirections_self 2

section Units

open _root_.Units.QuantityDimensions _root_.Units.EngineeringQuantities

-- Units of the compliance in the form `J = F * (F / k)`: a force times a force over a
-- translational stiffness is an energy.
example : forceDim * (forceDim / translationalStiffnessDim) = energyDim := by
  rw [tipDisplacement_dimension, compliance_dimension]

end Units

/-- **Nonzero force and stiffness errors.** The design `F = 2`, `k = 2` (compliance `2`) and the
estimate `Fhat = 3/2`, `khat = 3` (compliance `3/4`) are admissible for `Fmax = 2` and the
positive lower stiffness bound `kmin = 2`. The intermediate compliance `J(3/2, 2) = 9/8` splits
the error `5/4` into the force step `7/8` and the stiffness step `3/8`, and the composed bound
`(2 Fmax / kmin) |F - Fhat| + (Fmax² / kmin²) |k - khat|` evaluates to `2`. -/
lemma compliance_error_fixture :
    compliance 2 2 = 2 ∧ compliance (3 / 2) 3 = 3 / 4 ∧ compliance (3 / 2) 2 = 9 / 8 ∧
      |compliance 2 2 - compliance (3 / 2) 3| ≤
        (2 * 2 / 2) * |(2 : ℝ) - 3 / 2| + (2 ^ 2 / 2 ^ 2) * |(2 : ℝ) - 3| ∧
      (2 * 2 / 2) * |(2 : ℝ) - 3 / 2| + (2 ^ 2 / 2 ^ 2) * |(2 : ℝ) - 3| = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold compliance tipDisplacement
    norm_num
  · unfold compliance tipDisplacement
    norm_num
  · unfold compliance tipDisplacement
    norm_num
  · exact abs_compliance_sub_compliance_le (Fmax := 2) (kmin := 2) (F := 2) (Fhat := 3 / 2)
      (k := 2) (khat := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · norm_num

-- A supplied model term: the analysis-model compliance `1` lies within `1/4` of the compliance
-- `3/4` at the estimated inputs, and the discretized, solved and computed values equal it; the
-- reference compliance `2` is then within `2 + 1/4` of the computed value `1`.
example : |compliance 2 2 - 1| ≤
    (2 * 2 / 2) * |(2 : ℝ) - 3 / 2| + (2 ^ 2 / 2 ^ 2) * |(2 : ℝ) - 3| + 1 / 4 + 0 + 0 + 0 := by
  refine abs_compliance_sub_computed_le (Fmax := 2) (kmin := 2) (F := 2) (Fhat := 3 / 2) (k := 2)
    (khat := 3) (Jmodel := 1) (Jdisc := 1) (Jsolve := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num) (by norm_num)
  rw [(compliance_error_fixture).2.1]
  norm_num

-- A residual with the stability constant `1 / kmin`: for `kmin = 1`, `k = 2`, `F = 2` and the
-- trial `u = 3/2` the residual is `1`, the state error is `1/2 ≤ 1` and the compliance error is
-- `1 ≤ 2`.
example : |tipDisplacement 2 2 - 3 / 2| ≤ |2 * (3 / 2) - 2| / 1 ∧
    |compliance 2 2 - 2 * (3 / 2)| ≤ |(2 : ℝ)| * |2 * (3 / 2) - 2| / 1 :=
  abs_sub_le_residual_div (by norm_num) (by norm_num)

-- A bare residual is not a compliance error: for `F = 2`, no constant `C` bounds the compliance
-- error by `C` times the residual over all stiffnesses `k > 0`.
example : ¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |compliance 2 k - 2 * u| ≤ C * |k * u - 2| :=
  (not_exists_residual_error_bound (by norm_num)).2

-- The state-error half needs no condition on the force: even for `F = 0`, no constant `C` bounds
-- the state error by `C` times the residual over all stiffnesses `k > 0`.
example : ¬ ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |tipDisplacement 0 k - u| ≤ C * |k * u - 0| :=
  not_exists_residual_state_error_bound 0

-- The compliance half does need `F ≠ 0`: at `F = 0` the compliance error vanishes, so the constant
-- `0` bounds it by the residual.
example : ∃ C : ℝ, ∀ k u : ℝ, 0 < k → |compliance 0 k - 0 * u| ≤ C * |k * u - 0| :=
  ⟨0, fun _ _ _ => by simp [compliance, tipDisplacement]⟩

end PhyslibExtTest.Statistics.DesignSensitivity

end
