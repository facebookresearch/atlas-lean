/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.CombustionPorts

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Numerical.Certified

/-!
# Tests for `PhyslibExt.Chemistry.CombustionPorts`

Amounts in moles; air carries `3.76` mol of nitrogen per mol of oxygen.

* complete methane combustion is a nonzero balanced reaction;
* a fuel-rich charge in air (`1` mol methane, `1.5` mol oxygen) cannot burn completely: oxygen
  limits and the maximal feasible extent is `0.75` mol;
* a stoichiometric charge in air (`1` mol methane, `2` mol oxygen) burns completely to `1` mol
  carbon dioxide and `2` mol water, with the nitrogen unchanged;
* synthetic constant-heat-capacity enthalpies (not property data): `1` mol methane, `3` mol
  oxygen and `4` mol nitrogen at `300` burn completely with heat release `2000` and total product
  heat capacity `9`; the residual `9 (T - 300) - 2000` changes sign on `[300, 1000]` and its unique
  root `4700 / 9` lies in `[522, 523]`; the residual is minus the heat release at the inlet, does
  not depend on the elemental reference, and is constant without products.
-/

@[expose] public section

namespace PhyslibExtTest.Chemistry.CombustionPorts

open _root_.Chemistry.Stoichiometry _root_.Chemistry.Thermodynamics _root_.Chemistry.CombustionPorts
  _root_.MathlibExt.Analysis.Numerical.Certified

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

-- Synthetic adiabatic-temperature fixture.

/-- Synthetic constant-heat-capacity enthalpies for the methane species, not property data:
`H s T = h s + c s * (T - 300)` with `h = (0, 0, -1000, -500, 0)` and `c = (1, 1, 2, 1, 1)` on
`CH4, O2, CO2, H2O, N2`. -/
noncomputable def syntheticEnthalpy : Species → ℝ → ℝ
  | .CH4, T => T - 300
  | .O2, T => T - 300
  | .CO2, T => -1000 + 2 * (T - 300)
  | .H2O, T => -500 + (T - 300)
  | .N2, T => T - 300

/-- The residual of the synthetic fixture: one methane, three oxygen and four nitrogen enter at
`300` and burn completely (`ξ = 1`) to `O2 = 1`, `CO2 = 1`, `H2O = 2`, `N2 = 4`. -/
noncomputable def syntheticResidual (T : ℝ) : ℝ :=
  enthalpyResidual syntheticEnthalpy (reactantCharge 1 3 4)
    (reactantCharge 1 3 4 + (1 : ℝ) • methaneCombustion) 300 T

-- The synthetic fixture has heat release `2000` and the constant-heat-capacity residual
-- `9 * (T - 300) - 2000`, total heat capacity `9`.
example :
    heatRelease syntheticEnthalpy methaneCombustion 1 300 = 2000 ∧
      ∀ T, syntheticResidual T = 9 * (T - 300) - 2000 := by
  have huniv : (Finset.univ : Finset Species) = {.CH4, .O2, .CO2, .H2O, .N2} := rfl
  have hsum : ∀ f : Species → ℝ, ∑ i, f i = f .CH4 + f .O2 + f .CO2 + f .H2O + f .N2 := by
    intro f
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  constructor
  · simp only [heatRelease, reactionEnthalpy_apply, hsum, syntheticEnthalpy, methaneCombustion]
    norm_num
  · intro T
    simp only [syntheticResidual, enthalpyResidual, hsum, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, reactantCharge, methaneCombustion, syntheticEnthalpy]
    ring

-- The synthetic residual changes sign on `[300, 1000]` (`-2000` and `4300`), and its unique
-- root there, `4700 / 9`, lies in the rational interval `[522, 523]`.
example :
    syntheticResidual 300 < 0 ∧ 0 < syntheticResidual 1000 ∧
      ∃ Tad, (⟨522, 523⟩ : RatInterval).Encloses Tad ∧ syntheticResidual Tad = 0 ∧
        ∀ T ∈ Set.Icc (300 : ℝ) 1000, syntheticResidual T = 0 → T = Tad := by
  have hR : ∀ T, syntheticResidual T = 9 * (T - 300) - 2000 := by
    have huniv : (Finset.univ : Finset Species) = {.CH4, .O2, .CO2, .H2O, .N2} := rfl
    have hsum : ∀ f : Species → ℝ, ∑ i, f i = f .CH4 + f .O2 + f .CO2 + f .H2O + f .N2 := by
      intro f
      rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      ring
    intro T
    simp only [syntheticResidual, enthalpyResidual, hsum, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, reactantCharge, methaneCombustion, syntheticEnthalpy]
    ring
  refine ⟨?_, ?_, 4700 / 9, ?_, ?_, ?_⟩
  · rw [hR 300]
    norm_num
  · rw [hR 1000]
    norm_num
  · show (4700 / 9 : ℝ) ∈ Set.Icc ((_ : ℚ) : ℝ) ((_ : ℚ) : ℝ)
    constructor <;> norm_num
  · rw [hR]
    norm_num
  · intro T _ h0
    rw [hR] at h0
    linarith

-- `enthalpyResidual_inlet`: at the inlet temperature the synthetic residual is minus the heat
-- release.
example : syntheticResidual 300 = -heatRelease syntheticEnthalpy methaneCombustion 1 300 :=
  enthalpyResidual_inlet _ _ _ _ _

-- Reference-state invariance (`enthalpyResidual_shift_of_isBalanced`): shifting the synthetic
-- enthalpies by element potentials `e` leaves the residual unchanged.
example (e : Element → ℝ) (T : ℝ) :
    enthalpyResidual (fun i T' => syntheticEnthalpy i T' + ∑ b, composition b i * e b)
        (reactantCharge 1 3 4) (reactantCharge 1 3 4 + (1 : ℝ) • methaneCombustion) 300 T =
      syntheticResidual T :=
  enthalpyResidual_shift_of_isBalanced composition syntheticEnthalpy e _ _ _ _ _
    isBalanced_methaneCombustion

-- Invalid: with all product amounts zero the residual is constant, so it is not strictly
-- increasing on `[300, 1000]` (`not_strictMonoOn_enthalpyResidual_zero`).
example :
    ¬ StrictMonoOn (enthalpyResidual syntheticEnthalpy (reactantCharge 1 3 4) 0 300)
      (Set.Icc 300 1000) :=
  not_strictMonoOn_enthalpyResidual_zero _ _ (by norm_num)

-- `existsUnique_adiabaticTemperature_methane` on the synthetic data: the charge is nonnegative,
-- `ξ = 1` is feasible, the molar heat capacities `(1, 1, 2, 1, 1)` are positive and are the
-- derivatives of the linear enthalpies, and the residual changes sign on `[300, 1000]`.
example : ∃! Tad, Tad ∈ Set.Icc (300 : ℝ) 1000 ∧ syntheticResidual Tad = 0 := by
  have hR : ∀ T, syntheticResidual T = 9 * (T - 300) - 2000 := by
    have huniv : (Finset.univ : Finset Species) = {.CH4, .O2, .CO2, .H2O, .N2} := rfl
    have hsum : ∀ f : Species → ℝ, ∑ i, f i = f .CH4 + f .O2 + f .CO2 + f .H2O + f .N2 := by
      intro f
      rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      ring
    intro T
    simp only [syntheticResidual, enthalpyResidual, hsum, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, reactantCharge, methaneCombustion, syntheticEnthalpy]
    ring
  have hfeas : (1 : ℝ) ∈ forwardFeasibleExtents methaneCombustion (reactantCharge 1 3 4) := by
    refine ⟨zero_le_one, fun i => ?_⟩
    cases i <;> norm_num [reactantCharge, methaneCombustion]
  show ∃! Tad, Tad ∈ Set.Icc (300 : ℝ) 1000 ∧ enthalpyResidual syntheticEnthalpy
    (reactantCharge 1 3 4) (reactantCharge 1 3 4 + (1 : ℝ) • methaneCombustion) 300 Tad = 0
  refine existsUnique_adiabaticTemperature_methane
    (cp := fun s _ => match s with
      | .CH4 => 1 | .O2 => 1 | .CO2 => 2 | .H2O => 1 | .N2 => 1)
    (fun i => by cases i <;> norm_num [reactantCharge]) hfeas one_pos
    (by norm_num : (300 : ℝ) < 1000) ?_ ?_ ?_ ?_
  · intro T _ j
    cases j
    · exact (hasDerivAt_id' T).sub_const 300
    · exact (hasDerivAt_id' T).sub_const 300
    · have h := (((hasDerivAt_id' T).sub_const 300).const_mul 2).const_add (-1000)
      rw [mul_one] at h
      exact h
    · exact ((hasDerivAt_id' T).sub_const 300).const_add (-500)
    · exact (hasDerivAt_id' T).sub_const 300
  · intro T _ j
    cases j <;> norm_num
  · have h := hR 300
    unfold syntheticResidual at h
    rw [h]
    norm_num
  · have h := hR 1000
    unfold syntheticResidual at h
    rw [h]
    norm_num

end PhyslibExtTest.Chemistry.CombustionPorts
