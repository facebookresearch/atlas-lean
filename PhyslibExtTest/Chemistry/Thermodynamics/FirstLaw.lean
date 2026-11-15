/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FirstLaw

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum

/-!

# Tests for the first-law module

Instances of each result with computed values, the reference-independence of internal-energy
differences, and boundary cases: Lean's junk values outside the physical domain, a heat loop
through a nonpositive temperature, an adiabatic coefficient other than `n * R` that only the
algebraic pressure identity accepts, equal volumes, and an inadmissible external pressure for
which the work comparison fails.

-/

@[expose] public section

open Chemistry.Thermodynamics

namespace PhyslibExtTest.Chemistry.Thermodynamics

/-!

## A. Ideal-gas quantities

-/

/-- Internal-energy differences do not depend on the reference state. -/
example (T₁ T₂ : ℝ) :
    internalEnergy 3 0 0 T₂ - internalEnergy 3 0 0 T₁ =
      internalEnergy 3 100 298 T₂ - internalEnergy 3 100 298 T₁ := by
  rw [internalEnergy_sub, internalEnergy_sub]

/-- At the reference temperature the internal energy is the reference energy. -/
example : internalEnergy 3 100 298 298 = 100 := by
  simp [internalEnergy]

/-- Outside the physical domain the definitions return Lean's junk value `0`. -/
example : idealGasP 1 1 1 0 = 0 ∧ heatCapacityRatio 5 0 = 0 := by
  simp [idealGasP, heatCapacityRatio]

/-!

## B. Heat and internal energy as 1-forms

-/

-- Heat path dependence instance: `n = R = Cv = 1` on the rectangle
-- `[1, 2] × [1, 2]` gives different path integrals.
example : pathRightUp (heatCoeffV 1 1) (heatCoeffT 1)
      1 2 1 2
    ≠ pathUpRight (heatCoeffV 1 1) (heatCoeffT 1)
      1 2 1 2 :=
  heat_twoPaths_differ 1 1 1 1 2 1 2
    zero_lt_one zero_lt_one (by norm_num) zero_lt_one (by norm_num)

/-- The path-dependence result also holds outside the physical domain, as a fact about the
1-form: this loop passes through the nonphysical temperature `T₁ = -1`. -/
example : pathRightUp (heatCoeffV 1 1) (heatCoeffT 1) 1 2 (-1) 1
    ≠ pathUpRight (heatCoeffV 1 1) (heatCoeffT 1) 1 2 (-1) 1 :=
  heat_twoPaths_differ 1 1 1 (-1) 1 1 2
    zero_lt_one zero_lt_one (by norm_num) zero_lt_one (by norm_num)

-- Energy path independence instance: `U = V + T` on `[1, 2] × [1, 2]`.
example : pathRightUp (fun _ _ : ℝ => 1) (fun _ _ : ℝ => 1) 1 2 1 2
    = pathUpRight (fun _ _ : ℝ => 1) (fun _ _ : ℝ => 1) 1 2 1 2 := by
  have hPderiv : ∀ T ∈ ({1, 2} : Set ℝ), ∀ V ∈ Set.uIcc (1:ℝ) 2,
      HasDerivAt (fun V : ℝ => V + T) 1 V := by
    intro T _ V _
    have h := (hasDerivAt_id' V).add (hasDerivAt_const V T)
    rw [add_zero] at h
    exact h
  have hQderiv : ∀ V ∈ ({1, 2} : Set ℝ), ∀ T ∈ Set.uIcc (1:ℝ) 2,
      HasDerivAt (fun T : ℝ => V + T) 1 T := by
    intro V _ T _
    have h := (hasDerivAt_const T V).add (hasDerivAt_id' T)
    rw [zero_add] at h
    exact h
  have hPint : ∀ T ∈ ({1, 2} : Set ℝ),
      IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 1 2 :=
    fun _ _ => intervalIntegrable_const
  have hQint : ∀ V ∈ ({1, 2} : Set ℝ),
      IntervalIntegrable (fun _ : ℝ => (1:ℝ)) MeasureTheory.volume 1 2 :=
    fun _ _ => intervalIntegrable_const
  exact exact_twoPaths_equal (fun V T : ℝ => V + T) (fun _ _ : ℝ => 1)
    (fun _ _ : ℝ => 1) 1 2 1 2 hPderiv hPint hQderiv hQint

/-!

## C. Reversible isothermal work

-/

-- Reversible isothermal work with a computed numeric value: `n = 2`, `R = 3`,
-- `T = 1`, `V₁ = 1`, `V₂ = e` gives `w = -6`.
example : isothermalWorkOn 2 3 1 1 (Real.exp 1) = -6 := by
  unfold isothermalWorkOn
  simp only [div_one, Real.log_exp]
  norm_num

-- The reversible isothermal integral agrees with the closed form numerically.
example : (∫ V in (1:ℝ)..Real.exp 1,
    -(idealGasP 2 3 1 V) ∂MeasureTheory.volume) = -6 := by
  rw [isothermal_work 2 3 1 1 (Real.exp 1) zero_lt_one (Real.exp_pos 1)]
  unfold isothermalWorkOn
  simp only [div_one, Real.log_exp]
  norm_num

-- Boundary case: equal volumes give zero reversible isothermal work.
example (n R T V : ℝ) (hV : 0 < V) :
    isothermalWorkOn n R T V V = 0 := by
  unfold isothermalWorkOn
  rw [div_self (ne_of_gt hV), Real.log_one, mul_zero, neg_zero]

/-!

## D. Reversible adiabatic processes

-/

/-- A monatomic ideal gas (`Cv = 3/2`, `nR = 1`, so `γ = 5/3`) compressed reversibly and
adiabatically to an eighth of its volume heats up by the factor `8 ^ (2/3) = 4`. -/
example (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (had : (3 / 2 : ℝ) * Real.log (T₂ / T₁) + 1 * Real.log (1 / 8) = 0) :
    T₂ / T₁ = 4 := by
  rw [adiabatic_invariant_ratio_T T₁ T₂ 8 1 (3 / 2) 1 (5 / 3) hT₁ hT₂ (by norm_num) one_pos
    (by norm_num) (by norm_num) had]
  rw [show (8 : ℝ) / 1 = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `adiabatic_path_integrated` applies to the process `V t = 1 + t`, `T t = 1 / (1 + t)` on
`[0, 1]` (`T * V` is constant: the reversible adiabat for `Cv = nR = 1`), although `V` is not
positive for every real parameter (`V (-2) = -1`). -/
example : (1 : ℝ) * Real.log ((1 / (1 + 1)) / (1 / (1 + 0))) +
    1 * Real.log ((1 + 1) / (1 + 0)) = 0 := by
  have hpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < 1 + t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    linarith [ht.1]
  have hV : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
    intro t _
    have h := (hasDerivAt_id' t).const_add (1 : ℝ)
    exact h
  have hT : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 1 / (1 + t)) (-1 / (1 + t) ^ 2) t := by
    intro t ht
    have h := (hV t ht).inv (hpos t ht).ne'
    simp only [one_div]
    convert h using 1
  have hcont : ContinuousOn (fun t : ℝ => 1 + t) (Set.uIcc 0 1) := by fun_prop
  have hTc : ContinuousOn (fun t : ℝ => 1 / (1 + t)) (Set.uIcc 0 1) :=
    continuousOn_const.div hcont fun t ht => (hpos t ht).ne'
  have hT'c : ContinuousOn (fun t : ℝ => -1 / (1 + t) ^ 2) (Set.uIcc 0 1) :=
    continuousOn_const.div (hcont.pow 2) fun t ht => pow_ne_zero 2 (hpos t ht).ne'
  exact adiabatic_path_integrated (fun t : ℝ => 1 / (1 + t)) (fun t : ℝ => 1 + t)
    (fun t => -1 / (1 + t) ^ 2) (fun _ => 1) 1 1 hT hV
    (fun t ht => one_div_pos.mpr (hpos t ht)) hpos
    ((hT'c.div hTc fun t ht => one_div_ne_zero (hpos t ht).ne').intervalIntegrable)
    ((continuousOn_const.div hcont fun t ht => (hpos t ht).ne').intervalIntegrable)
    (fun t ht => by
      have h := (hpos t ht).ne'
      field_simp
      ring)

/-- That volume is not positive for every real parameter, so global-parameter hypotheses would
exclude the process above. -/
example : ¬ ∀ t : ℝ, 0 < 1 + t := fun h => by linarith [h (-2)]

/-- The `p * V ^ γ` invariant for `γ = 2`, `Cv = n = R = 1` between the states
`(T, V) = (1, e)` and `(e, 1)`. -/
example : idealGasP 1 1 (Real.exp 1) 1 * (1:ℝ) ^ (2:ℝ)
    = idealGasP 1 1 1 (Real.exp 1) * (Real.exp 1) ^ (2:ℝ) := by
  have had : (1:ℝ) * Real.log (Real.exp 1 / 1) + 1 * 1 * Real.log (1 / Real.exp 1)
      = 0 := by
    rw [div_one, one_div, Real.log_inv, Real.log_exp]
    norm_num
  have hγ : (2:ℝ) - 1 = 1 * 1 / 1 := by norm_num
  exact adiabatic_invariant_pV 1 1 1 (Real.exp 1) (Real.exp 1) 1 1 2
    zero_lt_one zero_lt_one zero_lt_one (Real.exp_pos 1) (Real.exp_pos 1)
    zero_lt_one one_ne_zero hγ had

/-- The pressure ratio for the same gas (`Cv = n = R = 1`, `γ = 2`) compressed reversibly and
adiabatically from `(T, V) = (1, 2)` to `(2, 1)`: the pressure rises by `2 ^ 2 = 4`. -/
example : idealGasP 1 1 2 1 / idealGasP 1 1 1 2 = 4 := by
  have had : (1:ℝ) * Real.log (2 / 1) + 1 * 1 * Real.log (1 / 2) = 0 := by
    rw [div_one, one_div, Real.log_inv]
    ring
  rw [adiabatic_invariant_ratio_p 1 1 1 2 2 1 1 2 zero_lt_one zero_lt_one zero_lt_one
    two_pos two_pos zero_lt_one one_ne_zero (by norm_num) had]
  norm_num

/-- The algebraic identity accepts a coefficient `k = 2` that is not the `n * R = 1` of the
pressure model (`Cv = 1`, so `γ = 3`): the states `(T, V) = (1, 2)` and `(4, 1)` satisfy its
hypotheses. -/
example : idealGasP 1 1 4 1 * (1:ℝ) ^ (3:ℝ) = idealGasP 1 1 1 2 * (2:ℝ) ^ (3:ℝ) := by
  have had : (1:ℝ) * Real.log (4 / 1) + 2 * Real.log (1 / 2) = 0 := by
    rw [div_one, one_div, Real.log_inv, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  exact idealGasP_mul_rpow_of_log_relation 1 1 1 4 2 1 1 2 3
    zero_lt_one zero_lt_one zero_lt_one (by norm_num) two_pos zero_lt_one one_ne_zero
    (by norm_num) had

/-- The physical invariant ties `γ` to the gas: for `Cv = n = R = 1` its hypothesis
`γ - 1 = n * R / Cv` holds only for `γ = 2`, so it rejects the `γ = 3` of the example above. -/
example (γ : ℝ) (hγ : γ - 1 = 1 * 1 / 1) : γ = 2 := by
  linarith

/-- The `γ` chain: `γ = Cp / Cv = 5 / 3` with `Cp - Cv = nR = 2` gives `γ - 1 = nR / Cv`. -/
example (γ : ℝ) (hγ : γ = heatCapacityRatio 5 3) : γ - 1 = 2 / 3 :=
  gamma_sub_one 5 3 2 γ (by norm_num) hγ (by norm_num)

/-!

## E. Heat capacities

-/

/-- For `U = internalEnergy 3 100 298` and `nR = 2`, any `Cp` with `dH/dT = Cp` is `5`. -/
example (Cp T : ℝ) (h : HasDerivAt (enthalpyOf (internalEnergy 3 100 298) 2) Cp T) :
    Cp = 5 := by
  have := heatCapacity_difference _ Cp 3 2 T (hasDerivAt_internalEnergy 3 100 298 T) h
  linarith

/-- The constant-`Cv` enthalpy has derivative `Cv + nR = 5`. -/
example (T : ℝ) : HasDerivAt (enthalpyOf (internalEnergy 3 100 298) 2) 5 T := by
  have h := hasDerivAt_enthalpyOf_internalEnergy 3 2 100 298 T
  norm_num at h
  exact h

/-- Molar heat capacities of `n = 2` moles with `R = 1` and `Cv = 3` differ by `R`. -/
example (Cp T : ℝ) (h : HasDerivAt (enthalpyOf (internalEnergy 3 0 0) (2 * 1)) Cp T) :
    Cp / 2 - 3 / 2 = 1 :=
  molarHeatCapacity_difference _ Cp 3 2 1 T two_ne_zero (hasDerivAt_internalEnergy 3 0 0 T) h

/-!

## F. Reversible versus irreversible work

-/

-- Reversible/irreversible comparison instance: `n = R = T = 1`, `V₁ = 1`,
-- `V₂ = 2`, `p_ext = 1 / 2 = p_final`.
example : |irreversibleWorkOn (1 / 2) 1 2|
    ≤ |isothermalWorkOn 1 1 1 1 2| :=
  irreversible_le_reversible 1 1 1 1 2 (1 / 2)
    zero_lt_one zero_lt_one zero_lt_one zero_lt_one (by norm_num) (by norm_num)
    (by norm_num)

-- Boundary case: equal volumes give zero irreversible work.
example (p V : ℝ) : irreversibleWorkOn p V V = 0 := by
  unfold irreversibleWorkOn
  rw [sub_self, mul_zero, neg_zero]

-- Boundary case: an inadmissible external pressure (`p_ext = 10 > p_final`)
-- gives no comparison claim; here the inequality fails.
example : ¬ (|irreversibleWorkOn 10 1 2|
    ≤ |isothermalWorkOn 1 1 1 1 2|) := by
  have hL : |irreversibleWorkOn 10 1 2| = 10 := by
    unfold irreversibleWorkOn
    norm_num
  have hR : |isothermalWorkOn 1 1 1 1 2| = Real.log 2 := by
    unfold isothermalWorkOn
    simp only [div_one, one_mul, abs_neg]
    exact abs_of_nonneg (Real.log_nonneg (by norm_num))
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hle1 := Real.log_le_sub_one_of_pos h2pos
  rw [hL, hR]
  intro hle
  linarith

end PhyslibExtTest.Chemistry.Thermodynamics
