/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.CombustionPorts

import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Chemistry.CombustionPorts`

Amounts in moles; air carries `3.76` mol of nitrogen per mol of oxygen.

* complete methane combustion is a nonzero balanced reaction;
* a fuel-rich charge in air (`1` mol methane, `1.5` mol oxygen) cannot burn completely: oxygen
  limits and the maximal feasible extent is `0.75` mol;
* a stoichiometric charge in air (`1` mol methane, `2` mol oxygen) burns completely to `1` mol
  carbon dioxide and `2` mol water, with the nitrogen unchanged.
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.CombustionPorts

open _root_.Chemistry.Stoichiometry _root_.Chemistry.CombustionPorts

-- A nonzero balanced reaction.
example :
    methaneCombustion ≠ 0 ∧ IsBalanced composition methaneCombustion := by
  refine ⟨?_, isBalanced_methaneCombustion⟩
  intro h
  have hCH4 := congrFun h Species.CH4
  simp only [methaneCombustion, Pi.zero_apply] at hCH4
  norm_num at hCH4

-- A fuel-rich input: `1` mol methane in air with `1.5` mol oxygen and `5.64` mol nitrogen
-- (equivalence ratio `4 / 3`). Complete combustion is infeasible, oxygen limits, and the maximal
-- feasible extent is `0.75` mol.
example :
    (1 : ℝ) ∉ forwardFeasibleExtents methaneCombustion (reactantCharge 1 1.5 5.64) ∧
      IsLimitingReagent methaneCombustion (reactantCharge 1 1.5 5.64) .O2 ∧
      maxExtent methaneCombustion (reactantCharge 1 1.5 5.64) methaneCombustion_consumes =
        0.75 := by
  have hn₀ : ∀ i, 0 ≤ reactantCharge 1 1.5 5.64 i := by
    intro i
    cases i <;> norm_num [reactantCharge]
  have hO2lt : reactantCharge 1 1.5 5.64 .O2 < 2 * reactantCharge 1 1.5 5.64 .CH4 := by
    norm_num [reactantCharge]
  have hO2le : reactantCharge 1 1.5 5.64 .O2 ≤ 2 * reactantCharge 1 1.5 5.64 .CH4 := by
    norm_num [reactantCharge]
  refine ⟨?_, isLimitingReagent_O2 hn₀ hO2le, ?_⟩
  · exact complete_not_mem_of_oxygen_lt hO2lt
  · rw [maxExtent_methaneCombustion]
    norm_num [reactantCharge]

-- A stoichiometric input: `1` mol methane in air with `2` mol oxygen and `7.52` mol nitrogen.
-- Complete combustion is feasible and leaves no methane or oxygen, `1` mol carbon dioxide, `2` mol
-- water and the `7.52` mol nitrogen.
example :
    (1 : ℝ) ∈ forwardFeasibleExtents methaneCombustion (reactantCharge 1 2 7.52) ∧
      reactantCharge 1 2 7.52 + (1 : ℝ) • methaneCombustion =
        fun s => match s with
          | .CH4 => 0
          | .O2 => 0
          | .CO2 => 1
          | .H2O => 2
          | .N2 => 7.52 := by
  have hn₀ : ∀ i, 0 ≤ reactantCharge 1 2 7.52 i := by
    intro i
    cases i <;> norm_num [reactantCharge]
  have hmem : reactantCharge 1 2 7.52 .CH4 ∈
      forwardFeasibleExtents methaneCombustion (reactantCharge 1 2 7.52) := by
    rw [complete_mem_forwardFeasibleExtents_iff hn₀]
    norm_num [reactantCharge]
  refine ⟨hmem, ?_⟩
  funext s
  cases s <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, reactantCharge,
    methaneCombustion] <;> norm_num

end PhyslibExtTest.Chemistry.CombustionPorts
