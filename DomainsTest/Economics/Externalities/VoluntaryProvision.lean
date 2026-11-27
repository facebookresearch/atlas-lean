/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Externalities.VoluntaryProvision
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fin.VecNotation

/-! Two consumers with logarithmic common benefit and a positive marginal benefit at zero. -/

open Set Filter MathlibExt.Economics.PublicGood
open scoped NNReal Topology

namespace VoluntaryProvisionTest

private noncomputable def value (x : ℝ) := Real.log (1 + x)

private noncomputable def marginal (x : ℝ) := (1 + x)⁻¹

private theorem value_deriv {x : ℝ} (hx : 0 ≤ x) : HasDerivAt value (marginal x) x := by
  have h := ((hasDerivAt_id' x).const_add 1).log (by linarith : 1 + x ≠ 0)
  change HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 + x)⁻¹ x
  simpa only [one_div] using h

private theorem model : CommonBenefit value marginal where
  increasing := by
    intro x hx y hy hxy
    exact Real.log_le_log (by linarith [show 0 ≤ x from hx]) (by linarith : 1 + x ≤ 1 + y)
  concave := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy hne a b ha hb hab
    have hx' : 0 < 1 + x := by linarith [show 0 ≤ x from hx]
    have hy' : 0 < 1 + y := by linarith [show 0 ≤ y from hy]
    have h := strictConcaveOn_log_Ioi.2 hx' hy' (by simpa using hne : 1 + x ≠ 1 + y) ha hb hab
    have hshift : a • (1 + x) + b • (1 + y) = 1 + (a • x + b • y) := by
      simp only [smul_eq_mul]; linarith
    simpa only [value, hshift] using h
  marginal x hx := (value_deriv hx).hasDerivWithinAt
  vanishing := tendsto_inv_atTop_zero.comp (tendsto_const_nhds.add_atTop tendsto_id)

-- The levy here actually varies with the rival's contribution. The game masks the payer's slot.
private noncomputable def rivalCharge (_i : Fin 2) (g : Fin 2 → ℝ≥0) : ℝ := provision g

-- Unit cost is 1/2; one consumer alone can supply the private total 1, with the other inactive.
example : (contributionGame value (1 / 2) rivalCharge).IsNash ![1, 0] := by
  rw [isNash_iff_marginal_eq (by decide) model (by norm_num) (by norm_num [marginal])]
  norm_num [provision, marginal, Fin.sum_univ_two]

-- At the corrected price both single-contributor profiles of total 3 are equilibria,
-- whereas keeping the private profile of total 1 is not an equilibrium.
example : (contributionGame value (1 / 4) rivalCharge).IsNash ![3, 0] ∧
    (contributionGame value (1 / 4) rivalCharge).IsNash ![0, 3] ∧
    ¬ (contributionGame value (1 / 4) rivalCharge).IsNash ![1, 0] := by
  simp only [isNash_iff_marginal_eq (by decide : 0 < 2) model
    (by norm_num : 0 < (1 : ℝ) / 4) (by norm_num [marginal])]
  norm_num [provision, marginal, Fin.sum_univ_two]

-- Dropping the endpoint-price hypothesis is not innocuous, even for this same smooth,
-- strictly concave benefit: with price 2 the zero profile is Nash but marginal benefit is 1.
example : (contributionGame (n := 2) value 2 rivalCharge).IsNash 0 ∧ marginal 0 < 2 := by
  constructor
  · rw [contributionGame_isNash_iff]
    intro i x hx
    have hx' : 0 ≤ x := by simpa [provision] using hx
    change value x - 2 * x ≤ value (provision 0) - 2 * provision (0 : Fin 2 → ℝ≥0)
    simp only [provision, Pi.zero_apply, NNReal.coe_zero, Finset.sum_const_zero, value, add_zero,
      Real.log_one, mul_zero, sub_zero]
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)]
  · norm_num [marginal]

-- Fixed charges set at the efficient total leave excess tax revenue at zero contributions.
example : (∑ i, fixedCharge (matchingRate 2 (1 / 2)) 3 i (![0, 0] : Fin 2 → ℝ≥0)) >
    matchingRate 2 (1 / 2) * provision (![0, 0] : Fin 2 → ℝ≥0) := by
  norm_num [fixedCharge, matchingRate, provision, Fin.sum_univ_two]

end VoluntaryProvisionTest
