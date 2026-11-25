/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PhyslibExt.EarthScience.InternalEnergyMonotonic

/-!

# First law of thermodynamics for the ideal gas

Work, heat and internal energy of an ideal gas with constant heat capacities: the path
dependence of heat, reversible isothermal and adiabatic processes, the heat-capacity relation
`Cp - Cv = nR`, and reversible versus irreversible work.

## i. Overview

The first law is `ΔU = q + w` with the IUPAC sign convention: `w` is the work done on the
system. Reversible volume work is therefore `-∫ p dV`, and work against a constant external
pressure `p_ext` is `-p_ext * (V₂ - V₁)`. The internal energy is a state function, so its
differential is exact and `ΔU` does not depend on the path; heat is not exact, so `q` does.

The model is the ideal gas `p * V = n * R * T` with constant heat capacities. Its internal
energy is `U(T) = U₀ + Cv * (T - T₀)` relative to an explicit reference state `(T₀, U₀)`: a
constant `Cv` fixes only energy differences. Reversible paths are quasi-static, with the
external pressure equal to the gas pressure. Quantities are real numbers in consistent units,
and physical values are positive: `n, R, T, V > 0` and `Cv > 0`. Some definitions are total
functions that return Lean's junk values outside that domain (division by zero, the logarithm
of a nonpositive number); their docstrings say so. Each result assumes only the hypotheses its
proof uses. Where that leaves out part of the physical domain, the result's docstring or section
note says which part; the result then also holds outside the physical domain, where it is an
identity about the model's formulas rather than a statement about a gas.

Proved here: the heat 1-form `δq = p dV + Cv dT` has a nonzero loop integral, while an exact
differential has none; reversible isothermal work is `-(n * R * T * log (V₂ / V₁))`; along a
reversible adiabat `T * V ^ (γ - 1)` and `p * V ^ γ` are constant; `Cp - Cv = nR` for the
total heat capacities and `Cp / n - Cv / n = R` for the molar ones; and in an isothermal
expansion against a constant external pressure `p_ext ≤ p_final` the irreversible work is at
most the reversible work in magnitude.

## ii. Key results

- `heat_pathDependent`, `heat_twoPaths_differ` : heat depends on the path.
- `exact_loopIntegral_eq_zero`, `exact_twoPaths_equal` : an exact differential does not.
- `isothermal_work` : the reversible isothermal work of an ideal gas.
- `adiabatic_invariant_TV`, `adiabatic_invariant_pV` : the reversible adiabatic invariants.
- `idealGasP_ratio_of_log_relation`, `idealGasP_mul_rpow_of_log_relation` : the algebraic
  identities behind the pressure invariants, for an arbitrary coefficient in place of `n * R`.
- `heatCapacity_difference`, `molarHeatCapacity_difference` : Mayer's relation, total and molar.
- `hasDerivAt_enthalpyOf_internalEnergy` : `Cp = Cv + nR` for the constant-`Cv` ideal gas.
- `irreversible_le_reversible` : `|w_irr| ≤ |w_rev|` for admissible external pressures.

## iii. Table of contents

- A. Ideal-gas quantities
- B. Heat and internal energy as 1-forms
- C. Reversible isothermal work
- D. Reversible adiabatic processes
- E. Heat capacities
- F. Reversible versus irreversible work

## iv. References

- E. R. Cohen et al., *Quantities, Units and Symbols in Physical Chemistry* (the IUPAC Green
  Book), 3rd ed., RSC Publishing, 2007: the first law `ΔU = q + w`, with `w` the work done on the
  system.
- P. Atkins and J. de Paula, *Atkins' Physical Chemistry*, 9th ed., Oxford University Press,
  2010, Chapter 2, "The First Law": expansion work, adiabatic changes of a perfect gas and the
  relation between the heat capacities.

-/

@[expose] public section

namespace Chemistry.Thermodynamics

/-!

## A. Ideal-gas quantities

-/

/-- Ideal-gas pressure `p = n * R * T / V` of `n` moles at temperature `T` in volume `V` (model
assumption: the ideal-gas equation of state). Physical states have `V > 0`; at `V = 0` Lean's
convention `x / 0 = 0` gives the meaningless value `0`, and the results below use `idealGasP`
only for `V > 0`. -/
noncomputable def idealGasP (n R T V : ℝ) : ℝ := n * R * T / V

/-- Heat-capacity ratio `γ = Cp / Cv` (constant heat capacities). It is defined for `Cv ≠ 0`;
at `Cv = 0` Lean's convention `x / 0 = 0` gives the meaningless value `0`, and `gamma_sub_one`
assumes `Cv ≠ 0`. -/
noncomputable def heatCapacityRatio (Cp Cv : ℝ) : ℝ := Cp / Cv

/-- Internal energy of an ideal gas with constant heat capacity `Cv`, relative to a reference
state: `U(T) = U₀ + Cv * (T - T₀)`, where `U₀` is the energy at the reference temperature `T₀`.
A constant `Cv` determines only energy differences (`internalEnergy_sub`), so the reference is
an explicit parameter; in the ideal-gas model `U` does not depend on `V`. This is the model of
`EarthScience.internalEnergy_hasDerivAt`. -/
def internalEnergy (Cv U₀ T₀ T : ℝ) : ℝ := U₀ + Cv * (T - T₀)

/-- The constant-`Cv` internal energy changes by `Cv * (T₂ - T₁)`, whatever the reference
state. It is an identity of the model formula and holds for all real `Cv` and temperatures. -/
lemma internalEnergy_sub (Cv U₀ T₀ T₁ T₂ : ℝ) :
    internalEnergy Cv U₀ T₀ T₂ - internalEnergy Cv U₀ T₀ T₁ = Cv * (T₂ - T₁) := by
  simp only [internalEnergy]
  ring

/-- The constant-`Cv` internal energy has temperature derivative `Cv`, at every real `T` and for
every real `Cv`. -/
lemma hasDerivAt_internalEnergy (Cv U₀ T₀ T : ℝ) :
    HasDerivAt (internalEnergy Cv U₀ T₀) Cv T :=
  EarthScience.internalEnergy_hasDerivAt T

/-- Enthalpy `H(T) = U(T) + nR * T` of an ideal gas with internal energy `U`, from
`H = U + p * V` and `p * V = n * R * T`. -/
def enthalpyOf (U : ℝ → ℝ) (nR : ℝ) : ℝ → ℝ := fun T => U T + nR * T

/-!

## B. Heat and internal energy as 1-forms

For a reversible process of an ideal gas, `δq = dU - δw = Cv dT + p dV`. Line integrals of
`P dV + Q dT` are taken along axis-aligned paths in the `(V, T)` plane. The heat results below
use positive volumes but no sign of `T` or `Cv`: they hold for all real temperatures and `Cv`,
and their physical reading is the case `T > 0`, `Cv > 0`.

-/

/-- The `dV` coefficient of the reversible heat 1-form `δq = p dV + Cv dT` of an ideal gas: the
pressure `n * R * T / V`. Physical states have `V > 0`; at `V = 0` it is Lean's junk value
`0`. -/
noncomputable def heatCoeffV (n R : ℝ) : ℝ → ℝ → ℝ := fun V T => n * R * T / V

/-- The `dT` coefficient of the reversible heat 1-form `δq = p dV + Cv dT`: the constant-volume
heat capacity `Cv`. -/
def heatCoeffT (Cv : ℝ) : ℝ → ℝ → ℝ := fun _ _ => Cv

/-- Line integral of the 1-form `P dV + Q dT` around the axis-aligned rectangle
with volume range `[V₁, V₂]` and temperature range `[T₁, T₂]`, traversed
counterclockwise from `(V₁, T₁)`. Each of the four legs is an interval integral; a leg whose
integrand is not integrable contributes `0` by convention. -/
noncomputable def rectLoopIntegral (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) : ℝ :=
  (∫ V in V₁..V₂, P V T₁ ∂MeasureTheory.volume) +
    (∫ T in T₁..T₂, Q V₂ T ∂MeasureTheory.volume) +
    (∫ V in V₂..V₁, P V T₂ ∂MeasureTheory.volume) +
    (∫ T in T₂..T₁, Q V₁ T ∂MeasureTheory.volume)

/-- Line integral of `P dV + Q dT` from `(V₁, T₁)` to `(V₂, T₂)` along the
"right then up" path: first at constant `T₁`, then at constant `V₂`. Each leg is an interval
integral; a leg whose integrand is not integrable contributes `0` by convention. -/
noncomputable def pathRightUp (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) : ℝ :=
  (∫ V in V₁..V₂, P V T₁ ∂MeasureTheory.volume) +
    (∫ T in T₁..T₂, Q V₂ T ∂MeasureTheory.volume)

/-- Line integral of `P dV + Q dT` from `(V₁, T₁)` to `(V₂, T₂)` along the
"up then right" path: first at constant `V₁`, then at constant `T₂`. Each leg is an interval
integral; a leg whose integrand is not integrable contributes `0` by convention. -/
noncomputable def pathUpRight (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) : ℝ :=
  (∫ T in T₁..T₂, Q V₁ T ∂MeasureTheory.volume) +
    (∫ V in V₁..V₂, P V T₂ ∂MeasureTheory.volume)

/-- Integral of a constant over volume: `∫ V in V₁..V₂, c / V = c * log (V₂ / V₁)`. -/
private lemma integral_const_div (c V₁ V₂ : ℝ) (hV₁ : 0 < V₁) (hV : V₁ ≤ V₂) :
    (∫ V in V₁..V₂, c / V ∂MeasureTheory.volume) = c * Real.log (V₂ / V₁) := by
  have hV₂ : 0 < V₂ := lt_of_lt_of_le hV₁ hV
  have hinv : (∫ V in V₁..V₂, V⁻¹ ∂MeasureTheory.volume) = Real.log (V₂ / V₁) :=
    integral_inv_of_pos hV₁ hV₂
  have hfun : (fun V : ℝ => c / V) = (fun V => c * V⁻¹) := by
    funext V
    rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul c _, hinv]

/-- The rectangular loop integral of an exact energy differential vanishes (path independence),
given the partial derivatives of `U` and their integrability along the edges of the rectangle. -/
lemma exact_loopIntegral_eq_zero (U dUdV dUdT : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ)
    (hPderiv : ∀ T ∈ ({T₁, T₂} : Set ℝ), ∀ V ∈ Set.uIcc V₁ V₂,
      HasDerivAt (fun V => U V T) (dUdV V T) V)
    (hPint : ∀ T ∈ ({T₁, T₂} : Set ℝ),
      IntervalIntegrable (fun V => dUdV V T) MeasureTheory.volume V₁ V₂)
    (hQderiv : ∀ V ∈ ({V₁, V₂} : Set ℝ), ∀ T ∈ Set.uIcc T₁ T₂,
      HasDerivAt (fun T => U V T) (dUdT V T) T)
    (hQint : ∀ V ∈ ({V₁, V₂} : Set ℝ),
      IntervalIntegrable (fun T => dUdT V T) MeasureTheory.volume T₁ T₂) :
    rectLoopIntegral dUdV dUdT V₁ V₂ T₁ T₂ = 0 := by
  have hT₁ : T₁ ∈ ({T₁, T₂} : Set ℝ) := Set.mem_insert _ _
  have hT₂ : T₂ ∈ ({T₁, T₂} : Set ℝ) := Set.mem_insert_of_mem _ rfl
  have hV₁ : V₁ ∈ ({V₁, V₂} : Set ℝ) := Set.mem_insert _ _
  have hV₂ : V₂ ∈ ({V₁, V₂} : Set ℝ) := Set.mem_insert_of_mem _ rfl
  have eB : (∫ V in V₁..V₂, dUdV V T₁ ∂MeasureTheory.volume) = U V₂ T₁ - U V₁ T₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun V hV => hPderiv T₁ hT₁ V hV)
      (hPint T₁ hT₁)
  have eR : (∫ T in T₁..T₂, dUdT V₂ T ∂MeasureTheory.volume) = U V₂ T₂ - U V₂ T₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun T hT => hQderiv V₂ hV₂ T hT)
      (hQint V₂ hV₂)
  have eT : (∫ V in V₂..V₁, dUdV V T₂ ∂MeasureTheory.volume) = U V₁ T₂ - U V₂ T₂ := by
    have hmem : ∀ V ∈ Set.uIcc V₂ V₁, HasDerivAt (fun V => U V T₂) (dUdV V T₂) V := by
      intro V hVmem
      rw [Set.uIcc_comm] at hVmem
      exact hPderiv T₂ hT₂ V hVmem
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hmem (hPint T₂ hT₂).symm
  have eL : (∫ T in T₂..T₁, dUdT V₁ T ∂MeasureTheory.volume) = U V₁ T₁ - U V₁ T₂ := by
    have hmem : ∀ T ∈ Set.uIcc T₂ T₁, HasDerivAt (fun T => U V₁ T) (dUdT V₁ T) T := by
      intro T hTmem
      rw [Set.uIcc_comm] at hTmem
      exact hQderiv V₁ hV₁ T hTmem
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hmem (hQint V₁ hV₁).symm
  simp only [rectLoopIntegral]
  rw [eB, eR, eT, eL]
  ring

/-- A rectangle loop integral is the difference of the two spanning path integrals. -/
private lemma loop_eq_paths_sub (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) :
    rectLoopIntegral P Q V₁ V₂ T₁ T₂
      = pathRightUp P Q V₁ V₂ T₁ T₂ - pathUpRight P Q V₁ V₂ T₁ T₂ := by
  have hT : (∫ V in V₂..V₁, P V T₂ ∂MeasureTheory.volume)
      = -(∫ V in V₁..V₂, P V T₂ ∂MeasureTheory.volume) :=
    intervalIntegral.integral_symm V₁ V₂
  have hL : (∫ T in T₂..T₁, Q V₁ T ∂MeasureTheory.volume)
      = -(∫ T in T₁..T₂, Q V₁ T ∂MeasureTheory.volume) :=
    intervalIntegral.integral_symm T₁ T₂
  simp only [rectLoopIntegral, pathRightUp, pathUpRight]
  rw [hT, hL]
  ring

/-- Exact energy differentials are path independent: the two spanning paths agree, given the
partial derivatives of `U` and their integrability along the edges of the rectangle. -/
lemma exact_twoPaths_equal (U dUdV dUdT : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ)
    (hPderiv : ∀ T ∈ ({T₁, T₂} : Set ℝ), ∀ V ∈ Set.uIcc V₁ V₂,
      HasDerivAt (fun V => U V T) (dUdV V T) V)
    (hPint : ∀ T ∈ ({T₁, T₂} : Set ℝ),
      IntervalIntegrable (fun V => dUdV V T) MeasureTheory.volume V₁ V₂)
    (hQderiv : ∀ V ∈ ({V₁, V₂} : Set ℝ), ∀ T ∈ Set.uIcc T₁ T₂,
      HasDerivAt (fun T => U V T) (dUdT V T) T)
    (hQint : ∀ V ∈ ({V₁, V₂} : Set ℝ),
      IntervalIntegrable (fun T => dUdT V T) MeasureTheory.volume T₁ T₂) :
    pathRightUp dUdV dUdT V₁ V₂ T₁ T₂ = pathUpRight dUdV dUdT V₁ V₂ T₁ T₂ := by
  have hloop :=
    exact_loopIntegral_eq_zero U dUdV dUdT V₁ V₂ T₁ T₂ hPderiv hPint hQderiv hQint
  have hsub := loop_eq_paths_sub dUdV dUdT V₁ V₂ T₁ T₂
  rw [hloop] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- Closed rectangular loop integral of the heat 1-form in closed form. Only `0 < V₁ ≤ V₂` is
used: the formula holds for all real `n`, `R`, `Cv`, `T₁` and `T₂`. -/
lemma heat_loopIntegral_eq (n R Cv T₁ T₂ V₁ V₂ : ℝ) (hV₁ : 0 < V₁)
    (hV : V₁ ≤ V₂) :
    rectLoopIntegral (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂
      = n * R * (T₁ - T₂) * Real.log (V₂ / V₁) := by
  have eB : (∫ V in V₁..V₂, n * R * T₁ / V ∂MeasureTheory.volume)
      = (n * R * T₁) * Real.log (V₂ / V₁) :=
    integral_const_div (n * R * T₁) V₁ V₂ hV₁ hV
  have eT : (∫ V in V₂..V₁, n * R * T₂ / V ∂MeasureTheory.volume)
      = -(n * R * T₂ * Real.log (V₂ / V₁)) := by
    have hbase := integral_const_div (n * R * T₂) V₁ V₂ hV₁ hV
    have hsymm : (∫ V in V₂..V₁, n * R * T₂ / V ∂MeasureTheory.volume)
        = -(∫ V in V₁..V₂, n * R * T₂ / V ∂MeasureTheory.volume) :=
      intervalIntegral.integral_symm V₁ V₂
    rw [hsymm, hbase]
  have eR : (∫ T in T₁..T₂, Cv ∂MeasureTheory.volume) = (T₂ - T₁) * Cv := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have eL : (∫ T in T₂..T₁, Cv ∂MeasureTheory.volume) = (T₁ - T₂) * Cv := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  simp only [rectLoopIntegral, heatCoeffV, heatCoeffT]
  rw [eB, eT, eR, eL]
  ring

/-- The heat 1-form is path dependent: for `0 < n`, `0 < R` and `0 < V₁ < V₂`, its rectangular
loop integral is nonzero. It assumes nothing about the temperatures beyond `T₁ ≠ T₂` and nothing
about `Cv`, so it also holds for nonpositive temperatures outside the physical domain, where it is
a fact about the 1-form `n * R * T / V dV + Cv dT` rather than about a gas. The physical
heat-path statement is the case `0 < T₁`, `0 < T₂`, `0 < Cv`. -/
lemma heat_pathDependent (n R Cv T₁ T₂ V₁ V₂ : ℝ) (hn : 0 < n) (hR : 0 < R)
    (hT : T₁ ≠ T₂) (hV₁ : 0 < V₁) (hV : V₁ < V₂) :
    rectLoopIntegral (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂ ≠ 0 := by
  rw [heat_loopIntegral_eq n R Cv T₁ T₂ V₁ V₂ hV₁ (le_of_lt hV)]
  have hlog : Real.log (V₂ / V₁) ≠ 0 := by
    have hlt : (1 : ℝ) < V₂ / V₁ := by
      rw [lt_div_iff₀ hV₁, one_mul]
      exact hV
    exact ne_of_gt (Real.log_pos hlt)
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (ne_of_gt hn) (ne_of_gt hR)) (sub_ne_zero.mpr hT)) hlog

/-- Heat is path dependent: for `0 < n`, `0 < R` and `0 < V₁ < V₂`, the two spanning path
integrals differ. Like `heat_pathDependent`, it holds for all real `T₁ ≠ T₂` and every `Cv`,
nonpositive temperatures included, where it describes the 1-form rather than a gas; the physical
statement is the case `0 < T₁`, `0 < T₂`, `0 < Cv`. -/
lemma heat_twoPaths_differ (n R Cv T₁ T₂ V₁ V₂ : ℝ) (hn : 0 < n) (hR : 0 < R)
    (hT : T₁ ≠ T₂) (hV₁ : 0 < V₁) (hV : V₁ < V₂) :
    pathRightUp (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂
      ≠ pathUpRight (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂ := by
  have hloop := heat_pathDependent n R Cv T₁ T₂ V₁ V₂ hn hR hT hV₁ hV
  have hsub := loop_eq_paths_sub (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂
  intro heq
  rw [heq, sub_self] at hsub
  exact hloop hsub

/-!

## C. Reversible isothermal work

-/

/-- Reversible isothermal work done on `n` moles of ideal gas at temperature `T` taken from
volume `V₁` to `V₂`: `w = -(n * R * T * log (V₂ / V₁))`. Physical volumes are positive; for
`V₁ ≤ 0` or `V₂ ≤ 0`, `Real.log` returns `log |V₂ / V₁|` (and `0` at `0`), a meaningless value,
and `isothermal_work` assumes `0 < V₁` and `0 < V₂`. -/
noncomputable def isothermalWorkOn (n R T V₁ V₂ : ℝ) : ℝ :=
  -(n * R * T * Real.log (V₂ / V₁))

/-- Reversible isothermal ideal-gas work done on the system.
The ideal-gas equation and reversibility enter as the explicit integrand
`-p dV` with `p = n * R * T / V` at constant `T`. Only the positive volumes are used: the
identity holds for all real `n`, `R` and `T`, and its physical case is `n, R, T > 0`. -/
lemma isothermal_work (n R T V₁ V₂ : ℝ) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    (∫ V in V₁..V₂, -(idealGasP n R T V) ∂MeasureTheory.volume)
      = isothermalWorkOn n R T V₁ V₂ := by
  have hfun : (fun V : ℝ => -(idealGasP n R T V)) = (fun V => (-(n * R * T)) / V) := by
    funext V
    simp only [idealGasP]
    rw [neg_div]
  rcases le_total V₁ V₂ with hle | hle
  · have hbase := integral_const_div (-(n * R * T)) V₁ V₂ hV₁ hle
    rw [hfun, hbase]
    simp only [isothermalWorkOn]
    ring
  · have hbase := integral_const_div (-(n * R * T)) V₂ V₁ hV₂ hle
    have hsymm : (∫ V in V₁..V₂, -(idealGasP n R T V) ∂MeasureTheory.volume)
        = -(∫ V in V₂..V₁, -(idealGasP n R T V) ∂MeasureTheory.volume) :=
      intervalIntegral.integral_symm V₂ V₁
    have hlog : Real.log (V₁ / V₂) = -Real.log (V₂ / V₁) := by
      have hdiv : V₁ / V₂ = (V₂ / V₁)⁻¹ := (inv_div _ _).symm
      rw [hdiv, Real.log_inv]
    rw [hsymm, hfun, hbase, hlog]
    simp only [isothermalWorkOn]
    ring

/-!

## D. Reversible adiabatic processes

Along a reversible adiabat of the constant-`Cv` ideal gas, `dU = δw` gives
`Cv * dT = -p dV = -n * R * T * dV / V`, the separated equation
`Cv * dT / T + n * R * dV / V = 0`. It is a hypothesis of the results below. The results about
`T` and `V` alone write the coefficient `n * R` as one parameter `nR`. The pressure invariants
`adiabatic_invariant_ratio_p` and `adiabatic_invariant_pV` use the `n * R` of `idealGasP n R`
itself, so the adiabatic equation belongs to the gas whose pressure they state; their algebraic
forms `idealGasP_ratio_of_log_relation` and `idealGasP_mul_rpow_of_log_relation` accept any
coefficient.

Physical gases have `0 < Cv` and `0 < nR`. The results below need at most `Cv ≠ 0`, and those
with a parameter `nR` hold for every real `nR`; outside the physical domain they are identities
about the formulas.

-/

/-- From `Cp - Cv = nR` and `γ = Cp / Cv`: `γ - 1 = nR / Cv`. An algebraic identity: it needs
only `Cv ≠ 0`. -/
lemma gamma_sub_one (Cp Cv nR γ : ℝ) (hCv : Cv ≠ 0)
    (hγ : γ = heatCapacityRatio Cp Cv) (hCpCv : Cp - Cv = nR) :
    γ - 1 = nR / Cv := by
  rw [hγ]
  simp only [heatCapacityRatio]
  have hC : Cp / Cv - 1 = (Cp - Cv) / Cv := by
    field_simp
  rw [hC, hCpCv]

/-- Along a reversible adiabatic path, the log-invariant `log T + (γ - 1) * log V` has vanishing
derivative at a time where the separated ODE `Cv * dT / T + nR * dV / V = 0` holds, for `T, V > 0`,
`Cv ≠ 0` and `γ - 1 = nR / Cv`. -/
lemma adiabatic_invariant_hasDerivAt (T V T' V' : ℝ → ℝ) (Cv nR γ t : ℝ)
    (hT : HasDerivAt T (T' t) t) (hV : HasDerivAt V (V' t) t)
    (hTpos : 0 < T t) (hVpos : 0 < V t)
    (hCv : Cv ≠ 0)
    (hODE : Cv * (T' t / T t) + nR * (V' t / V t) = 0)
    (hγ : γ - 1 = nR / Cv) :
    HasDerivAt (fun t => Real.log (T t) + (γ - 1) * Real.log (V t)) 0 t := by
  have hlogT : HasDerivAt (fun t => Real.log (T t)) (T' t / T t) t :=
    hT.log (ne_of_gt hTpos)
  have hmul : HasDerivAt (fun t => (γ - 1) * Real.log (V t))
      ((γ - 1) * (V' t / V t)) t :=
    (hV.log (ne_of_gt hVpos)).const_mul (γ - 1)
  have hadd := hlogT.add hmul
  have hzero : T' t / T t + (γ - 1) * (V' t / V t) = 0 := by
    have hTt : T t ≠ 0 := ne_of_gt hTpos
    have hVt : V t ≠ 0 := ne_of_gt hVpos
    have hkey : T' t / T t + nR / Cv * (V' t / V t)
        = (1 / Cv) * (Cv * (T' t / T t) + nR * (V' t / V t)) := by
      field_simp
    rw [hγ, hkey, hODE, mul_zero]
  rw [hzero] at hadd
  exact hadd

/-- Integrating the separated adiabatic ODE along a path parameterized by `t ∈ [0, 1]` gives
the logarithmic relation between the endpoint states. Every hypothesis is required only on the
process interval `[0, 1]`. -/
lemma adiabatic_path_integrated (T V T' V' : ℝ → ℝ) (Cv nR : ℝ)
    (hT : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt T (T' t) t)
    (hV : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt V (V' t) t)
    (hTpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < T t)
    (hVpos : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < V t)
    (hTint : IntervalIntegrable (fun t => T' t / T t) MeasureTheory.volume 0 1)
    (hVint : IntervalIntegrable (fun t => V' t / V t) MeasureTheory.volume 0 1)
    (hODE : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Cv * (T' t / T t) + nR * (V' t / V t) = 0) :
    Cv * Real.log (T 1 / T 0) + nR * Real.log (V 1 / V 0) = 0 := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := Set.left_mem_uIcc
  have h1 : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := Set.right_mem_uIcc
  have eT : (∫ t in (0:ℝ)..1, T' t / T t ∂MeasureTheory.volume)
      = Real.log (T 1) - Real.log (T 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (hT t ht).log (ne_of_gt (hTpos t ht))) hTint
  have eV : (∫ t in (0:ℝ)..1, V' t / V t ∂MeasureTheory.volume)
      = Real.log (V 1) - Real.log (V 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (hV t ht).log (ne_of_gt (hVpos t ht))) hVint
  have hzero : (∫ t in (0:ℝ)..1,
      (Cv * (T' t / T t) + nR * (V' t / V t)) ∂MeasureTheory.volume) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun t ht => hODE t ht)]
    simp
  have hsplit : (∫ t in (0:ℝ)..1,
      (Cv * (T' t / T t) + nR * (V' t / V t)) ∂MeasureTheory.volume)
      = Cv * (Real.log (T 1) - Real.log (T 0))
        + nR * (Real.log (V 1) - Real.log (V 0)) := by
    rw [intervalIntegral.integral_add (hTint.const_mul Cv) (hVint.const_mul nR),
      intervalIntegral.integral_const_mul Cv _,
      intervalIntegral.integral_const_mul nR _, eT, eV]
  have hT0 : T 0 ≠ 0 := ne_of_gt (hTpos 0 h0)
  have hT1 : T 1 ≠ 0 := ne_of_gt (hTpos 1 h1)
  have hV0 : V 0 ≠ 0 := ne_of_gt (hVpos 0 h0)
  have hV1 : V 1 ≠ 0 := ne_of_gt (hVpos 1 h1)
  rw [Real.log_div hT1 hT0, Real.log_div hV1 hV0, ← hsplit, hzero]

/-- Reversible adiabatic invariant in ratio form: for positive temperatures and volumes, `Cv ≠ 0`,
`γ - 1 = nR / Cv` and `Cv * log (T₂ / T₁) + nR * log (V₂ / V₁) = 0`,
`T₂ / T₁ = (V₁ / V₂) ^ (γ - 1)`. -/
lemma adiabatic_invariant_ratio_T (T₁ T₂ V₁ V₂ Cv nR γ : ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv)
    (had : Cv * Real.log (T₂ / T₁) + nR * Real.log (V₂ / V₁) = 0) :
    T₂ / T₁ = (V₁ / V₂) ^ (γ - 1) := by
  have hV21 : Real.log (V₂ / V₁) = -Real.log (V₁ / V₂) := by
    have hdiv : V₂ / V₁ = (V₁ / V₂)⁻¹ := (inv_div _ _).symm
    rw [hdiv, Real.log_inv]
  have hlogT : Real.log (T₂ / T₁) = (γ - 1) * Real.log (V₁ / V₂) := by
    have h1 : Cv * Real.log (T₂ / T₁) = -(nR * Real.log (V₂ / V₁)) := by
      linear_combination had
    have h2 : Real.log (T₂ / T₁) = (-(nR * Real.log (V₂ / V₁))) / Cv := by
      rw [← h1]
      field_simp
    rw [h2, hV21, hγ]
    ring
  have hTpos : 0 < T₂ / T₁ := div_pos hT₂ hT₁
  have hVpos : 0 < V₁ / V₂ := div_pos hV₁ hV₂
  have hrpow : Real.exp ((γ - 1) * Real.log (V₁ / V₂)) = (V₁ / V₂) ^ (γ - 1) := by
    rw [mul_comm, Real.rpow_def_of_pos hVpos]
  calc T₂ / T₁ = Real.exp (Real.log (T₂ / T₁)) := (Real.exp_log hTpos).symm
    _ = Real.exp ((γ - 1) * Real.log (V₁ / V₂)) := by rw [hlogT]
    _ = (V₁ / V₂) ^ (γ - 1) := hrpow

/-- Reversible adiabatic invariant: for positive temperatures and volumes, `Cv ≠ 0`,
`γ - 1 = nR / Cv` and `Cv * log (T₂ / T₁) + nR * log (V₂ / V₁) = 0`, `T * V ^ (γ - 1)` takes the
same value at both states. -/
lemma adiabatic_invariant_TV (T₁ T₂ V₁ V₂ Cv nR γ : ℝ)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv)
    (had : Cv * Real.log (T₂ / T₁) + nR * Real.log (V₂ / V₁) = 0) :
    T₂ * V₂ ^ (γ - 1) = T₁ * V₁ ^ (γ - 1) := by
  have hratio := adiabatic_invariant_ratio_T T₁ T₂ V₁ V₂ Cv nR γ
    hT₁ hT₂ hV₁ hV₂ hCv hγ had
  have hdiv : (V₁ / V₂) ^ (γ - 1) = V₁ ^ (γ - 1) / V₂ ^ (γ - 1) :=
    Real.div_rpow (le_of_lt hV₁) (le_of_lt hV₂) (γ - 1)
  have hT₁' : T₁ ≠ 0 := ne_of_gt hT₁
  have hV₂r : V₂ ^ (γ - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hV₂ (γ - 1))
  rw [hdiv] at hratio
  field_simp at hratio ⊢
  linear_combination hratio

/-- Pressure ratio of the ideal-gas model `idealGasP n R` between two states with positive
temperatures and volumes related by `Cv * log (T₂ / T₁) + k * log (V₂ / V₁) = 0` with
`γ - 1 = k / Cv`, for an arbitrary coefficient `k`: `p₂ / p₁ = (V₁ / V₂) ^ γ`. This is an
algebraic identity, not the physical adiabat: `n * R` cancels from the pressure ratio, so `k` need
not be the `n * R` of the pressure model. The physical statement, with `k = n * R`, is
`adiabatic_invariant_ratio_p`. -/
lemma idealGasP_ratio_of_log_relation (n R T₁ T₂ V₁ V₂ Cv k γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = k / Cv)
    (had : Cv * Real.log (T₂ / T₁) + k * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ / idealGasP n R T₁ V₁ = (V₁ / V₂) ^ γ := by
  have hratio := adiabatic_invariant_ratio_T T₁ T₂ V₁ V₂ Cv k γ
    hT₁ hT₂ hV₁ hV₂ hCv hγ had
  have hVpos : 0 < V₁ / V₂ := div_pos hV₁ hV₂
  have hsplit : (V₁ / V₂) ^ ((γ - 1) + 1)
      = (V₁ / V₂) ^ (γ - 1) * (V₁ / V₂) ^ (1 : ℝ) :=
    Real.rpow_add hVpos (γ - 1) 1
  have hγeq : γ = (γ - 1) + 1 := by ring
  rw [hγeq, hsplit, Real.rpow_one, ← hratio]
  simp only [idealGasP]
  have hn' : n ≠ 0 := ne_of_gt hn
  have hR' : R ≠ 0 := ne_of_gt hR
  have hT₁' : T₁ ≠ 0 := ne_of_gt hT₁
  have hT₂' : T₂ ≠ 0 := ne_of_gt hT₂
  have hV₁' : V₁ ≠ 0 := ne_of_gt hV₁
  have hV₂' : V₂ ≠ 0 := ne_of_gt hV₂
  have hp₁ : n * R * T₁ / V₁ ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero hn' hR') hT₁') hV₁'
  field_simp

/-- Reversible adiabatic invariant in ratio form: `p₂ / p₁ = (V₁ / V₂) ^ γ` for the ideal gas
`idealGasP n R`. The relation `had`, which `adiabatic_path_integrated` gives with `nR = n * R`,
and `γ - 1 = n * R / Cv` carry the gas's own coefficient `n * R`. It needs only `Cv ≠ 0`; the
physical case is `0 < Cv`. -/
lemma adiabatic_invariant_ratio_p (n R T₁ T₂ V₁ V₂ Cv γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = n * R / Cv)
    (had : Cv * Real.log (T₂ / T₁) + n * R * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ / idealGasP n R T₁ V₁ = (V₁ / V₂) ^ γ :=
  idealGasP_ratio_of_log_relation n R T₁ T₂ V₁ V₂ Cv (n * R) γ
    hn hR hT₁ hT₂ hV₁ hV₂ hCv hγ had

/-- The ideal-gas `p * V ^ γ` takes equal values at two states with positive temperatures and
volumes related by `Cv * log (T₂ / T₁) + k * log (V₂ / V₁) = 0` with `γ - 1 = k / Cv`, for an
arbitrary coefficient `k`. Like `idealGasP_ratio_of_log_relation`, this is an algebraic identity:
`k` need not be the `n * R` of `idealGasP n R`. The physical statement, with `k = n * R`, is
`adiabatic_invariant_pV`. -/
lemma idealGasP_mul_rpow_of_log_relation (n R T₁ T₂ V₁ V₂ Cv k γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = k / Cv)
    (had : Cv * Real.log (T₂ / T₁) + k * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ * V₂ ^ γ = idealGasP n R T₁ V₁ * V₁ ^ γ := by
  have hratio := idealGasP_ratio_of_log_relation n R T₁ T₂ V₁ V₂ Cv k γ
    hn hR hT₁ hT₂ hV₁ hV₂ hCv hγ had
  have hdiv : (V₁ / V₂) ^ γ = V₁ ^ γ / V₂ ^ γ :=
    Real.div_rpow (le_of_lt hV₁) (le_of_lt hV₂) γ
  have hp₁ : idealGasP n R T₁ V₁ ≠ 0 := by
    have hpos : 0 < idealGasP n R T₁ V₁ := by
      simp only [idealGasP]
      exact div_pos (mul_pos (mul_pos hn hR) hT₁) hV₁
    exact ne_of_gt hpos
  have hV₂r : V₂ ^ γ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hV₂ γ)
  rw [hdiv] at hratio
  field_simp at hratio ⊢
  linear_combination hratio

/-- Reversible adiabatic invariant: `p * V ^ γ` is constant across states of the ideal gas
`idealGasP n R`. The relation `had`, which `adiabatic_path_integrated` gives with `nR = n * R`,
and `γ - 1 = n * R / Cv` carry the gas's own coefficient `n * R`. It needs only `Cv ≠ 0`; the
physical case is `0 < Cv`. -/
lemma adiabatic_invariant_pV (n R T₁ T₂ V₁ V₂ Cv γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = n * R / Cv)
    (had : Cv * Real.log (T₂ / T₁) + n * R * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ * V₂ ^ γ = idealGasP n R T₁ V₁ * V₁ ^ γ :=
  idealGasP_mul_rpow_of_log_relation n R T₁ T₂ V₁ V₂ Cv (n * R) γ
    hn hR hT₁ hT₂ hV₁ hV₂ hCv hγ had

/-!

## E. Heat capacities

These relations are identities about derivatives. They hold at every real temperature `T` and
for all real `Cv` and `nR` (in the molar form, every `n ≠ 0` and every real `R`), not only in
the physical domain where these quantities are positive.

-/

/-- For an ideal gas, `Cp - Cv = nR` for total heat capacities (Mayer's relation).
`Cp` is the temperature derivative of the enthalpy `H(T) = U(T) + nR * T`
and `Cv` the temperature derivative of the internal energy `U`. -/
lemma heatCapacity_difference (U : ℝ → ℝ) (Cp Cv nR T : ℝ)
    (hU : HasDerivAt U Cv T)
    (hH : HasDerivAt (enthalpyOf U nR) Cp T) :
    Cp - Cv = nR := by
  have hlin : HasDerivAt (fun T => nR * T) (nR * 1) T :=
    (hasDerivAt_id' T).const_mul nR
  have hadd : HasDerivAt (fun T => U T + nR * T) (Cv + nR * 1) T := hU.add hlin
  have huniq : Cp = Cv + nR * 1 := by
    rw [← hH.deriv]
    exact hadd.deriv
  linarith

/-- Molar form of Mayer's relation: for `n ≠ 0` moles with `H = U + n * R * T`, the molar heat
capacities `Cp / n` and `Cv / n` differ by the gas constant `R`. -/
lemma molarHeatCapacity_difference (U : ℝ → ℝ) (Cp Cv n R T : ℝ) (hn : n ≠ 0)
    (hU : HasDerivAt U Cv T) (hH : HasDerivAt (enthalpyOf U (n * R)) Cp T) :
    Cp / n - Cv / n = R := by
  have h := heatCapacity_difference U Cp Cv (n * R) T hU hH
  rw [← sub_div, h]
  field_simp

/-- Mayer's relation for the constant-`Cv` ideal gas: the enthalpy `U + nR * T` of
`internalEnergy Cv U₀ T₀` has temperature derivative `Cp = Cv + nR`, for every reference
state. -/
lemma hasDerivAt_enthalpyOf_internalEnergy (Cv nR U₀ T₀ T : ℝ) :
    HasDerivAt (enthalpyOf (internalEnergy Cv U₀ T₀) nR) (Cv + nR) T := by
  have h := (hasDerivAt_internalEnergy Cv U₀ T₀ T).add ((hasDerivAt_id' T).const_mul nR)
  rw [mul_one] at h
  exact h

/-!

## F. Reversible versus irreversible work

-/

/-- Work done on the system by a constant external pressure `p_ext` during a volume change from
`V₁` to `V₂`: `w = -(p_ext * (V₂ - V₁))`. -/
def irreversibleWorkOn (p_ext V₁ V₂ : ℝ) : ℝ := -(p_ext * (V₂ - V₁))

/-- For isothermal expansion (`0 < V₁ ≤ V₂`, positive `n`, `R`, `T`) between the same end states
with admissible constant `0 ≤ p_ext ≤ p_final`: `|w_irr| ≤ |w_rev|`. No unrestricted
irreversible-work comparison is claimed: the side hypotheses are essential. -/
lemma irreversible_le_reversible (n R T V₁ V₂ p_ext : ℝ)
    (hn : 0 < n) (hR : 0 < R) (hT : 0 < T)
    (hV₁ : 0 < V₁) (hV : V₁ ≤ V₂)
    (hp_ext : 0 ≤ p_ext)
    (hadm : p_ext ≤ n * R * T / V₂) :
    |irreversibleWorkOn p_ext V₁ V₂| ≤ |isothermalWorkOn n R T V₁ V₂| := by
  have hV₂ : 0 < V₂ := lt_of_lt_of_le hV₁ hV
  have hV₂' : V₂ ≠ 0 := ne_of_gt hV₂
  have hlog_nonneg : 0 ≤ Real.log (V₂ / V₁) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hV₁, one_mul]
    exact hV
  have hirr : |irreversibleWorkOn p_ext V₁ V₂| = p_ext * (V₂ - V₁) := by
    simp only [irreversibleWorkOn, abs_neg]
    exact abs_of_nonneg (mul_nonneg hp_ext (sub_nonneg.mpr hV))
  have hrev : |isothermalWorkOn n R T V₁ V₂| = n * R * T * Real.log (V₂ / V₁) := by
    simp only [isothermalWorkOn, abs_neg]
    exact abs_of_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hn) (le_of_lt hR)) (le_of_lt hT))
        hlog_nonneg)
  have hlog_key : 1 - V₁ / V₂ ≤ Real.log (V₂ / V₁) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hV₁ hV₂)
    have hinv : Real.log (V₁ / V₂) = -Real.log (V₂ / V₁) := by
      have hdiv : V₁ / V₂ = (V₂ / V₁)⁻¹ := (inv_div _ _).symm
      rw [hdiv, Real.log_inv]
    rw [hinv] at h
    linarith
  rw [hirr, hrev]
  have h1 : p_ext * (V₂ - V₁) ≤ (n * R * T / V₂) * (V₂ - V₁) :=
    mul_le_mul_of_nonneg_right hadm (sub_nonneg.mpr hV)
  have h2 : (n * R * T / V₂) * (V₂ - V₁) ≤ n * R * T * Real.log (V₂ / V₁) := by
    have hnRT : 0 < n * R * T := mul_pos (mul_pos hn hR) hT
    have hfrac : (V₂ - V₁) / V₂ ≤ Real.log (V₂ / V₁) := by
      have e : (V₂ - V₁) / V₂ = 1 - V₁ / V₂ := by
        field_simp
      rw [e]
      exact hlog_key
    have e2 : (n * R * T / V₂) * (V₂ - V₁) = n * R * T * ((V₂ - V₁) / V₂) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left hfrac (le_of_lt hnRT)
  exact h1.trans h2

end Chemistry.Thermodynamics
