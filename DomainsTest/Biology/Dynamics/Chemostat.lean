/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.Chemostat
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Tests for the chemostat

Concrete values of the vector field, the substrate equivalent and the interior steady state for
`μ_m = 2`, `K_s = 1`, `S_f = 1` (so `D_c = 1`); the threshold `D = D_c`, where the interior
formula gives the washout state; a quadrant steady state besides washout above `D_c` when the
yield is negative, which shows that `y > 0` is needed; and two non-vacuity witnesses for the
substrate-equivalent theorem, a nonconstant solution on the invariant line `X = 0` and the
interior steady state.
-/

open Filter Set Real
open scoped Topology
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)
open MathlibExt.Biology.Biophysics.SaturableElimination (steadyConc)
open Domains.Biology.Dynamics.Chemostat

namespace DomainsTest.Biology.Dynamics.Chemostat

example : vectorField (fun S ↦ S) 1 2 4 ![3, 1] = ![0, 1 / 4] := by
  ext i; fin_cases i <;> norm_num [vectorField]

example : substrateEquivalent 2 ![3, 1] = 5 / 2 := by norm_num [substrateEquivalent]

/-- A quotient by `0` is `0`: with `y = 0` the substrate equivalent is the substrate. -/
example : substrateEquivalent 0 ![3, 1] = 1 := by norm_num [substrateEquivalent]

/-- The critical dilution rate for `μ_m = 2`, `K_s = 1`, `S_f = 1`. -/
example : mmRate 2 1 1 = 1 := by norm_num [mmRate]

example : interiorState 2 1 (1 / 2) 1 1 = ![2 / 3, 1 / 3] := by
  ext i; fin_cases i <;> norm_num [interiorState, steadyConc]

example : vectorField (mmRate 2 1) (1 / 2) 1 1 (interiorState 2 1 (1 / 2) 1 1) = 0 := by
  ext i; fin_cases i <;> norm_num [interiorState, steadyConc, vectorField, mmRate]

/-- Below the threshold the steady states in the quadrant are washout and the interior state. -/
example : {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ vectorField (mmRate 2 1) (1 / 2) 1 1 x = 0} =
    {![0, 1], ![2 / 3, 1 / 3]} := by
  have h := ((equilibria_and_washout_threshold two_pos one_pos one_pos one_pos).2.2.2.1
    (1 / 2) (by norm_num) (by norm_num [mmRate])).1
  rw [h]
  congr 2
  ext i; fin_cases i <;> norm_num [interiorState, steadyConc]

/-- At the threshold `D = D_c` washout is the only steady state in the quadrant. -/
example : {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ vectorField (mmRate 2 1) 1 1 1 x = 0} =
    {![0, 1]} :=
  (equilibria_and_washout_threshold two_pos one_pos one_pos one_pos).2.2.1 1 one_pos
    (by norm_num [mmRate])

/-- At `D = D_c` the interior formula gives the washout state: the two steady states coalesce. -/
example : interiorState 2 1 1 1 1 = ![0, 1] := by
  ext i; fin_cases i <;> norm_num [interiorState, steadyConc]

/-- The formula's junk value at `D = μ_m`, where `μ_m - D = 0`. -/
example : interiorState 2 1 2 1 1 = ![1, 0] := by
  ext i; fin_cases i <;> norm_num [interiorState, steadyConc]

/-- The yield must be positive: with `y = -1` and `D = 3/2 ≥ D_c = 1`, the quadrant state
`(X, S) = (2, 3)` is a steady state besides washout. -/
example : vectorField (mmRate 2 1) (3 / 2) 1 (-1) ![2, 3] = 0 := by
  ext i; fin_cases i <;> norm_num [vectorField, mmRate]

/-- **Non-vacuity witness.** Without biomass, the substrate relaxes to the feed:
`X ≡ 0`, `S(t) = S_f + (S_0 - S_f) e^{-D t}` solves the chemostat balances on all of `ℝ`, for every
growth rate `μ`. -/
theorem isIntegralCurveOn_noBiomass (μ : ℝ → ℝ) (D Sf y S₀ : ℝ) :
    IsIntegralCurveOn (fun t ↦ ![0, Sf + (S₀ - Sf) * exp (-(D * t))])
      (fun _ ↦ vectorField μ D Sf y) univ := by
  intro t _
  refine hasDerivWithinAt_pi.2 fun i ↦ ?_
  fin_cases i
  · simpa using hasDerivWithinAt_const t univ (0 : ℝ)
  · have h := ((((hasDerivAt_id t).const_mul D).neg.exp).const_mul (S₀ - Sf)).const_add Sf
    convert h.hasDerivWithinAt using 1
    · ext s; simp
    · simp only [Fin.isValue, Fin.mk_one, vectorField_apply_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, mul_zero, zero_div, sub_zero]
      simp only [id, mul_one, Pi.neg_apply]
      ring

example (μ : ℝ → ℝ) (D Sf y S₀ : ℝ) (hD : 0 < D) :
    Tendsto (fun t ↦ substrateEquivalent y ![0, Sf + (S₀ - Sf) * exp (-(D * t))]) atTop
      (𝓝 Sf) :=
  (substrateEquivalent_relaxation ordConnected_univ (mem_univ 0)
    (isIntegralCurveOn_noBiomass μ D Sf y S₀)).2.2 hD (subset_univ _)

/-- **Non-vacuity witness with biomass.** The constant curve at the interior steady state solves
the balances, and its substrate equivalent is the feed. -/
example : substrateEquivalent 1 (interiorState 2 1 (1 / 2) 1 1) = 1 := by
  have hx : IsIntegralCurveOn (fun _ ↦ interiorState 2 1 (1 / 2) 1 1)
      (fun _ ↦ vectorField (mmRate 2 1) (1 / 2) 1 1) univ := by
    intro t _
    have h0 : vectorField (mmRate 2 1) (1 / 2) 1 1 (interiorState 2 1 (1 / 2) 1 1) = 0 := by
      ext i; fin_cases i <;> norm_num [interiorState, steadyConc, vectorField, mmRate]
    beta_reduce
    rw [h0]
    exact hasDerivWithinAt_const t univ _
  have hlim := (substrateEquivalent_relaxation ordConnected_univ (mem_univ 0) hx).2.2
    (by norm_num) (subset_univ _)
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end DomainsTest.Biology.Dynamics.Chemostat
