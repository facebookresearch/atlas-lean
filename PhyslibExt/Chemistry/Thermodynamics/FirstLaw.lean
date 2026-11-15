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

/-!
# First law of thermodynamics: work, heat, and ideal-gas processes

IUPAC sign convention: `w` is work done **on** the system. Reversible volume
work is therefore `-∫ p dV`, and work against a constant external pressure is
`-p_ext * (V₂ - V₁)`.

Model boundary:

* LAW: the first law `dU = δq + δw`. The internal energy `U` is a state
  function (exact differential `dU`); heat `δq` and work `δw` are inexact
  1-forms, so only `ΔU` is path independent.
* MOD: the ideal gas (`p * V = n * R * T`), constant heat capacities, and
  quasi-static reversibility taken as a limit (the external pressure equals
  the system pressure along reversible paths).
* MC: the proved consequences below: path (in)dependence of the heat form and
  the energy differential, reversible isothermal work, reversible adiabatic
  invariants, the heat-capacity relation, and the reversible/irreversible
  work comparison for admissible external pressures.
-/

@[expose] public section

namespace Chemistry.Thermodynamics

/-- Ideal-gas pressure `p = n * R * T / V` (MOD: ideal-gas equation of state). -/
noncomputable def idealGasP (n R T V : ℝ) : ℝ := n * R * T / V

/-- Heat-capacity ratio `γ = Cp / Cv` (MOD: constant heat capacities). -/
noncomputable def heatCapacityRatio (Cp Cv : ℝ) : ℝ := Cp / Cv

/-- Ideal-gas internal energy `U = Cv * T`: constant-`Cv` model, independent of `V` (MOD). -/
def internalEnergy (Cv T : ℝ) : ℝ := Cv * T

/-- Enthalpy `H(T) = U(T) + nR * T`, from `H = U + p * V` and `p * V = n * R * T` (MOD). -/
def enthalpyOf (U : ℝ → ℝ) (nR : ℝ) : ℝ → ℝ := fun T => U T + nR * T

/-- Reversible isothermal work done on the system, `w = -(n * R * T * log (V₂ / V₁))` (MC). -/
noncomputable def isothermalWorkOn (n R T V₁ V₂ : ℝ) : ℝ :=
  -(n * R * T * Real.log (V₂ / V₁))

/-- Work done on the system against a constant external pressure (MC). -/
def irreversibleWorkOn (p_ext V₁ V₂ : ℝ) : ℝ := -(p_ext * (V₂ - V₁))

/-- `dV`-coefficient of the heat 1-form `δq = P dV + Q dT`: the ideal-gas pressure. -/
noncomputable def heatCoeffV (n R : ℝ) : ℝ → ℝ → ℝ := fun V T => n * R * T / V

/-- `dT`-coefficient of the heat 1-form `δq = P dV + Q dT`: the constant-volume heat capacity. -/
def heatCoeffT (Cv : ℝ) : ℝ → ℝ → ℝ := fun _ _ => Cv

/-- Line integral of the 1-form `P dV + Q dT` around the axis-aligned rectangle
with volume range `[V₁, V₂]` and temperature range `[T₁, T₂]`, traversed
counterclockwise from `(V₁, T₁)`. -/
noncomputable def rectLoopIntegral (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) : ℝ :=
  (∫ V in V₁..V₂, P V T₁ ∂MeasureTheory.volume) +
    (∫ T in T₁..T₂, Q V₂ T ∂MeasureTheory.volume) +
    (∫ V in V₂..V₁, P V T₂ ∂MeasureTheory.volume) +
    (∫ T in T₂..T₁, Q V₁ T ∂MeasureTheory.volume)

/-- Line integral of `P dV + Q dT` from `(V₁, T₁)` to `(V₂, T₂)` along the
"right then up" path: first at constant `T₁`, then at constant `V₂`. -/
noncomputable def pathRightUp (P Q : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ) : ℝ :=
  (∫ V in V₁..V₂, P V T₁ ∂MeasureTheory.volume) +
    (∫ T in T₁..T₂, Q V₂ T ∂MeasureTheory.volume)

/-- Line integral of `P dV + Q dT` from `(V₁, T₁)` to `(V₂, T₂)` along the
"up then right" path: first at constant `V₁`, then at constant `T₂`. -/
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

/-- The loop integral of an exact energy differential vanishes (path independence, MC). -/
lemma exact_loopIntegral_eq_zero (U dUdV dUdT : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ)
    (hPderiv : ∀ T : ℝ, ∀ V ∈ Set.uIcc V₁ V₂,
      HasDerivAt (fun V => U V T) (dUdV V T) V)
    (hPint : ∀ T : ℝ,
      IntervalIntegrable (fun V => dUdV V T) MeasureTheory.volume V₁ V₂)
    (hQderiv : ∀ V : ℝ, ∀ T ∈ Set.uIcc T₁ T₂,
      HasDerivAt (fun T => U V T) (dUdT V T) T)
    (hQint : ∀ V : ℝ,
      IntervalIntegrable (fun T => dUdT V T) MeasureTheory.volume T₁ T₂) :
    rectLoopIntegral dUdV dUdT V₁ V₂ T₁ T₂ = 0 := by
  have eB : (∫ V in V₁..V₂, dUdV V T₁ ∂MeasureTheory.volume) = U V₂ T₁ - U V₁ T₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun V hV => hPderiv T₁ V hV) (hPint T₁)
  have eR : (∫ T in T₁..T₂, dUdT V₂ T ∂MeasureTheory.volume) = U V₂ T₂ - U V₂ T₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun T hT => hQderiv V₂ T hT) (hQint V₂)
  have eT : (∫ V in V₂..V₁, dUdV V T₂ ∂MeasureTheory.volume) = U V₁ T₂ - U V₂ T₂ := by
    have hmem : ∀ V ∈ Set.uIcc V₂ V₁, HasDerivAt (fun V => U V T₂) (dUdV V T₂) V := by
      intro V hVmem
      rw [Set.uIcc_comm] at hVmem
      exact hPderiv T₂ V hVmem
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hmem (hPint T₂).symm
  have eL : (∫ T in T₂..T₁, dUdT V₁ T ∂MeasureTheory.volume) = U V₁ T₁ - U V₁ T₂ := by
    have hmem : ∀ T ∈ Set.uIcc T₂ T₁, HasDerivAt (fun T => U V₁ T) (dUdT V₁ T) T := by
      intro T hTmem
      rw [Set.uIcc_comm] at hTmem
      exact hQderiv V₁ T hTmem
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hmem (hQint V₁).symm
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

/-- Exact energy differentials are path independent: the two spanning paths agree (MC). -/
lemma exact_twoPaths_equal (U dUdV dUdT : ℝ → ℝ → ℝ) (V₁ V₂ T₁ T₂ : ℝ)
    (hPderiv : ∀ T : ℝ, ∀ V ∈ Set.uIcc V₁ V₂,
      HasDerivAt (fun V => U V T) (dUdV V T) V)
    (hPint : ∀ T : ℝ,
      IntervalIntegrable (fun V => dUdV V T) MeasureTheory.volume V₁ V₂)
    (hQderiv : ∀ V : ℝ, ∀ T ∈ Set.uIcc T₁ T₂,
      HasDerivAt (fun T => U V T) (dUdT V T) T)
    (hQint : ∀ V : ℝ,
      IntervalIntegrable (fun T => dUdT V T) MeasureTheory.volume T₁ T₂) :
    pathRightUp dUdV dUdT V₁ V₂ T₁ T₂ = pathUpRight dUdV dUdT V₁ V₂ T₁ T₂ := by
  have hloop :=
    exact_loopIntegral_eq_zero U dUdV dUdT V₁ V₂ T₁ T₂ hPderiv hPint hQderiv hQint
  have hsub := loop_eq_paths_sub dUdV dUdT V₁ V₂ T₁ T₂
  rw [hloop] at hsub
  exact sub_eq_zero.mp hsub.symm

/-- Closed rectangular loop integral of the heat 1-form in closed form (MC). -/
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

/-- The heat 1-form is path dependent: its rectangular loop integral is nonzero (MC). -/
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

/-- Heat is path dependent: the two spanning path integrals differ (MC). -/
lemma heat_twoPaths_differ (n R Cv T₁ T₂ V₁ V₂ : ℝ) (hn : 0 < n) (hR : 0 < R)
    (hT : T₁ ≠ T₂) (hV₁ : 0 < V₁) (hV : V₁ < V₂) :
    pathRightUp (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂
      ≠ pathUpRight (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂ := by
  have hloop := heat_pathDependent n R Cv T₁ T₂ V₁ V₂ hn hR hT hV₁ hV
  have hsub := loop_eq_paths_sub (heatCoeffV n R) (heatCoeffT Cv) V₁ V₂ T₁ T₂
  intro heq
  rw [heq, sub_self] at hsub
  exact hloop hsub

/-- Reversible isothermal ideal-gas work done on the system (MC within MOD).
The ideal-gas equation and reversibility enter as the explicit integrand
`-p dV` with `p = n * R * T / V` at constant `T`. -/
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

/-- From `Cp - Cv = nR` and `γ = Cp / Cv`: `γ - 1 = nR / Cv` (MOD definitions). -/
lemma gamma_sub_one (Cp Cv nR γ : ℝ) (hCv : Cv ≠ 0)
    (hγ : γ = heatCapacityRatio Cp Cv) (hCpCv : Cp - Cv = nR) :
    γ - 1 = nR / Cv := by
  rw [hγ]
  simp only [heatCapacityRatio]
  have hC : Cp / Cv - 1 = (Cp - Cv) / Cv := by
    field_simp
  rw [hC, hCpCv]

/-- Along a reversible adiabatic path, the log-invariant has vanishing
derivative: the separated ODE `Cv * dT / T + nR * dV / V = 0` (MC). -/
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

/-- Integrating the separated adiabatic ODE along a path gives the logarithmic
relation between the endpoint states (MC). -/
lemma adiabatic_path_integrated (T V T' V' : ℝ → ℝ) (Cv nR : ℝ)
    (hT : ∀ t : ℝ, HasDerivAt T (T' t) t)
    (hV : ∀ t : ℝ, HasDerivAt V (V' t) t)
    (hTpos : ∀ t : ℝ, 0 < T t)
    (hVpos : ∀ t : ℝ, 0 < V t)
    (hTint : IntervalIntegrable (fun t => T' t / T t) MeasureTheory.volume 0 1)
    (hVint : IntervalIntegrable (fun t => V' t / V t) MeasureTheory.volume 0 1)
    (hODE : ∀ t : ℝ, Cv * (T' t / T t) + nR * (V' t / V t) = 0) :
    Cv * Real.log (T 1 / T 0) + nR * Real.log (V 1 / V 0) = 0 := by
  have eT : (∫ t in (0:ℝ)..1, T' t / T t ∂MeasureTheory.volume)
      = Real.log (T 1) - Real.log (T 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hT t).log (ne_of_gt (hTpos t))) hTint
  have eV : (∫ t in (0:ℝ)..1, V' t / V t ∂MeasureTheory.volume)
      = Real.log (V 1) - Real.log (V 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hV t).log (ne_of_gt (hVpos t))) hVint
  have hfun : (fun t : ℝ => Cv * (T' t / T t) + nR * (V' t / V t)) = fun _ => (0:ℝ) :=
    funext hODE
  have hzero : (∫ t in (0:ℝ)..1,
      (Cv * (T' t / T t) + nR * (V' t / V t)) ∂MeasureTheory.volume) = 0 := by
    rw [hfun, intervalIntegral.integral_const]
    simp
  have hsplit : (∫ t in (0:ℝ)..1,
      (Cv * (T' t / T t) + nR * (V' t / V t)) ∂MeasureTheory.volume)
      = Cv * (Real.log (T 1) - Real.log (T 0))
        + nR * (Real.log (V 1) - Real.log (V 0)) := by
    rw [intervalIntegral.integral_add (hTint.const_mul Cv) (hVint.const_mul nR),
      intervalIntegral.integral_const_mul Cv _,
      intervalIntegral.integral_const_mul nR _, eT, eV]
  have hT0 : T 0 ≠ 0 := ne_of_gt (hTpos 0)
  have hT1 : T 1 ≠ 0 := ne_of_gt (hTpos 1)
  have hV0 : V 0 ≠ 0 := ne_of_gt (hVpos 0)
  have hV1 : V 1 ≠ 0 := ne_of_gt (hVpos 1)
  rw [Real.log_div hT1 hT0, Real.log_div hV1 hV0, ← hsplit, hzero]

/-- Reversible adiabatic invariant in ratio form: `T₂ / T₁ = (V₁ / V₂) ^ (γ - 1)` (MC). -/
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

/-- Reversible adiabatic invariant: `T * V ^ (γ - 1)` is constant across states (MC). -/
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

/-- Reversible adiabatic invariant in ratio form: `p₂ / p₁ = (V₁ / V₂) ^ γ` (MC). -/
lemma adiabatic_invariant_ratio_p (n R T₁ T₂ V₁ V₂ Cv nR γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv)
    (had : Cv * Real.log (T₂ / T₁) + nR * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ / idealGasP n R T₁ V₁ = (V₁ / V₂) ^ γ := by
  have hratio := adiabatic_invariant_ratio_T T₁ T₂ V₁ V₂ Cv nR γ
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

/-- Reversible adiabatic invariant: `p * V ^ γ` is constant across states (MC). -/
lemma adiabatic_invariant_pV (n R T₁ T₂ V₁ V₂ Cv nR γ : ℝ)
    (hn : 0 < n) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hCv : Cv ≠ 0)
    (hγ : γ - 1 = nR / Cv)
    (had : Cv * Real.log (T₂ / T₁) + nR * Real.log (V₂ / V₁) = 0) :
    idealGasP n R T₂ V₂ * V₂ ^ γ = idealGasP n R T₁ V₁ * V₁ ^ γ := by
  have hratio := adiabatic_invariant_ratio_p n R T₁ T₂ V₁ V₂ Cv nR γ
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

/-- For an ideal gas, `Cp - Cv = nR` for total heat capacities (MC).
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

/-- Molar form: `cp - cv = R` per mole of ideal gas (MC). -/
lemma molarHeatCapacity_difference (u : ℝ → ℝ) (cp cv R T : ℝ)
    (hu : HasDerivAt u cv T)
    (hh : HasDerivAt (enthalpyOf u R) cp T) :
    cp - cv = R :=
  heatCapacity_difference u cp cv R T hu hh

/-- Constant-coefficient instance: with `U = a * T`, `(a + b) - a = b` (MC). -/
lemma heatCapacity_linear (a b T : ℝ) : (a + b) - a = b := by
  have hU : HasDerivAt (fun S : ℝ => internalEnergy a S) a T := by
    have h : HasDerivAt (fun S : ℝ => a * S) (a * 1) T :=
      (hasDerivAt_id' T).const_mul a
    rw [mul_one] at h
    simpa [internalEnergy] using h
  have hH : HasDerivAt (enthalpyOf (fun S : ℝ => internalEnergy a S) b) (a + b) T := by
    have h : HasDerivAt (fun S : ℝ => a * S + b * S) (a + b * 1) T :=
      hU.add ((hasDerivAt_id' T).const_mul b)
    rw [mul_one] at h
    change HasDerivAt (fun S : ℝ => a * S + b * S) (a + b) T
    exact h
  exact heatCapacity_difference _ _ _ _ _ hU hH

/-- For isothermal expansion between the same end states with admissible
constant `p_ext ≤ p_final`: `|w_irr| ≤ |w_rev|` (MC). No unrestricted
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
