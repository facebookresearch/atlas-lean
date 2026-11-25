/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import MathlibExt.Analysis.ODE.ConstantInputRelaxation

/-!
# Windkessel cardiovascular agreement

## i. Overview

The two-element Windkessel model `C p' = qin - p / R` with `R, C > 0` agrees with the canonical scalar evolution `k = 1/(RC)`, forcing `qin/C`: the constant-flow RC transient and the finite pressure-volume budget over `[0, T]`, `T >= 0`. Nonnegative pressure additionally requires nonnegative initial excess pressure/input; `R = 0` or `C = 0` is not this IVP.

## ii. Key results

* `windkessel_budget`: `C (p T - p 0)` equals the net inflow integral.
* `windkessel_transient`: the closed form solves the constant-flow equation.

## iii. Table of contents

* A. Windkessel agreement.

## iv. References

* The declared model is local to this module (the classical
  two-element Windkessel equation); no literature result is
  imported. All declarations are `lemma`s. The transient reuses
  `MathlibExt.Biology.Biophysics.CompartmentKinetics.amount`.
* Frank O. Die Grundform des arteriellen Pulses.
  Z Biol. 1899;37:483-526 (the original Windkessel model).

-/

@[expose] public section

open MeasureTheory intervalIntegral

/-! ## A. Windkessel agreement. -/

namespace PhyslibExt.Physiology.Windkessel

set_option linter.unusedVariables false in
/-- **Windkessel budget agreement.** For `R, C > 0`, if `p` solves
`C p' = qin - p / R` on `[0, T]` in derivative form, then the finite
pressure-volume budget holds:
`C * (p T - p 0) = ∫ s in 0..T, (qin s - p s / R)`. -/
lemma windkessel_budget {R C T : ℝ} (hR : 0 < R) (hC : 0 < C)
    (hT : 0 ≤ T) {p qin : ℝ → ℝ}
    (hp : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt p ((qin s - p s / R) / C) s)
    (hint : IntervalIntegrable (fun s => qin s - p s / R) volume 0 T) :
    C * (p T - p 0) = ∫ s in (0:ℝ)..T, (qin s - p s / R) := by
  have hCne : C ≠ 0 := ne_of_gt hC
  have hp' : ∀ s ∈ Set.uIcc 0 T, HasDerivAt p ((qin s - p s / R) / C) s := by
    rw [Set.uIcc_of_le hT]
    exact hp
  have hintC : IntervalIntegrable (fun s => (qin s - p s / R) / C) volume 0 T :=
    hint.div_const C
  have hftc : (∫ s in (0:ℝ)..T, (qin s - p s / R) / C) = p T - p 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hp' hintC
  have hdiv : (∫ s in (0:ℝ)..T, (qin s - p s / R) / C)
      = (∫ s in (0:ℝ)..T, (qin s - p s / R)) / C :=
    intervalIntegral.integral_div C _
  rw [hdiv] at hftc
  rw [← hftc]
  generalize (∫ s in (0:ℝ)..T, (qin s - p s / R)) = X
  field_simp

/-- **Constant-flow RC transient agreement.** The closed form
`p(t) = R * q + (p0 - R * q) * exp (-t / (R * C))` solves
`C p' = q - p / R` for constant flow `q`, at every `t`. -/
lemma windkessel_transient {R C q p0 t : ℝ} (hR : 0 < R) (hC : 0 < C) :
    C * deriv (fun u => R * q + (p0 - R * q) * Real.exp (-u / (R * C))) t =
      q - (R * q + (p0 - R * q) * Real.exp (-t / (R * C))) / R := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hCne : C ≠ 0 := ne_of_gt hC
  have hRCne : R * C ≠ 0 := mul_ne_zero hRne hCne
  have h1 : HasDerivAt (fun u : ℝ => u) 1 t := hasDerivAt_id' t
  have h2 : HasDerivAt (fun u : ℝ => -u) (-1) t := h1.neg
  have hlin : HasDerivAt (fun u : ℝ => -u / (R * C)) (-1 / (R * C)) t :=
    h2.div_const (R * C)
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u / (R * C)))
      (Real.exp (-t / (R * C)) * (-1 / (R * C))) t :=
    hlin.exp
  have hmul : HasDerivAt (fun u : ℝ => (p0 - R * q) * Real.exp (-u / (R * C)))
      ((p0 - R * q) * (Real.exp (-t / (R * C)) * (-1 / (R * C)))) t :=
    hexp.const_mul (p0 - R * q)
  have hfull : HasDerivAt
      (fun u : ℝ => R * q + (p0 - R * q) * Real.exp (-u / (R * C)))
      ((p0 - R * q) * (Real.exp (-t / (R * C)) * (-1 / (R * C)))) t :=
    hmul.const_add (R * q)
  rw [hfull.deriv]
  field_simp
  ring
/-- The Windkessel transient is the canonical one-compartment
amount with elimination rate `1 / (R * C)` and input `q / C`
(pressure-level correspondence: `p = amount (1/(RC)) (q/C) p0`),
with initial condition `p(0) = p0`. -/
lemma windkessel_amount_eq {R C q p0 : ℝ} (hR : 0 < R) (hC : 0 < C) :
    (fun t => R * q + (p0 - R * q) * Real.exp (-t / (R * C))) =
    MathlibExt.Biology.Biophysics.CompartmentKinetics.amount (1 / (R * C)) (q / C) p0 := by
  funext t
  have hk : (1 : ℝ) / (R * C) ≠ 0 := by positivity
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_eq_of_ne_zero hk]
  have hRC : R * C ≠ 0 := mul_ne_zero (ne_of_gt hR) (ne_of_gt hC)
  field_simp

/-- The Windkessel path starts at `p0`. -/
lemma windkessel_initial {R C q p0 : ℝ} (hR : 0 < R) (hC : 0 < C) :
    R * q + (p0 - R * q) * Real.exp (-(0:ℝ) / (R * C)) = p0 := by
  simp
/-- The Windkessel transient solves the pressure equation in
`HasDerivAt` form with derivative `(q - p t / R) / C`. -/
lemma windkessel_transient_hasDerivAt {R C q p0 t : ℝ} (hR : 0 < R)
    (hC : 0 < C) :
    HasDerivAt (fun u => R * q + (p0 - R * q) * Real.exp (-u / (R * C)))
      ((q - (R * q + (p0 - R * q) * Real.exp (-t / (R * C))) / R) / C) t := by
  have hamt := MathlibExt.Biology.Biophysics.CompartmentKinetics.hasDerivAt_amount
    (k := 1 / (R * C)) (R := q / C) (A₀ := p0) (t := t)
  rw [windkessel_amount_eq hR hC]
  convert hamt using 1
  have hk : (1 : ℝ) / (R * C) ≠ 0 := by
    have hRC : R * C ≠ 0 := mul_ne_zero (ne_of_gt hR) (ne_of_gt hC)
    positivity
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_eq_of_ne_zero hk]
  have hRC : R * C ≠ 0 := mul_ne_zero (ne_of_gt hR) (ne_of_gt hC)
  field_simp

end PhyslibExt.Physiology.Windkessel
