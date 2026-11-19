/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import MathlibExt.Biology.Biophysics.CompartmentKinetics

/-!
# Respiratory mechanics agreement

## i. Overview

The passive linear single-compartment equation `R V' + E V = Paw - P0` with `R, E > 0` and compliance `C = 1/E` agrees with the scalar evolution of decay `E/R` and forcing `(Paw - P0)/R`: the constant-drive closed form and free expiration. A jump in `Paw` is handled intervalwise; no derivative through a step is claimed.

## ii. Key results

* `respiratory_response`: the closed form solves `R V' + E V = dP`.
* `respiratory_expiration`: zero drive gives the pure decay solving `R V' + E V = 0`.

## iii. Table of contents

* A. Respiratory agreement.

## iv. References

* The declared model is local to this module; mechanical
  Kelvin-Voigt naming is not asserted. All declarations are
  `lemma`s. The closed forms reuse
  `MathlibExt.Biology.Biophysics.CompartmentKinetics.amount`.
* West JB, Luks AM. West's Respiratory Physiology: The Essentials.
  Wolters Kluwer (standard source for the linear single-compartment
  equation of motion `P = E V + R V'` used with these symbols).

-/

@[expose] public section

/-! ## A. Respiratory agreement. -/

namespace PhyslibExt.Physiology.RespiratoryMechanics

/-- **Single-compartment respiratory agreement.** With `R, E > 0`
and compliance `C = 1 / E`, the closed form
`V(t) = C * ΔP + (V0 - C * ΔP) * exp (-t / (R * C))` solves the
passive linear equation `R V' + E V = ΔP` at every `t` (constant
drive). -/
lemma respiratory_response {R E dP V0 t : ℝ} (hR : 0 < R) (hE : 0 < E) :
    R * deriv (fun u => (1 / E) * dP + (V0 - (1 / E) * dP) *
        Real.exp (-u / (R * (1 / E)))) t +
      E * ((1 / E) * dP + (V0 - (1 / E) * dP) *
        Real.exp (-t / (R * (1 / E)))) = dP := by
  have hE' : E ≠ 0 := ne_of_gt hE
  have hR' : R ≠ 0 := ne_of_gt hR
  have hX : R * (1 / E) ≠ 0 := mul_ne_zero hR' (one_div_ne_zero hE')
  have hexp : ∀ u : ℝ, -u / (R * (1 / E)) = (-(R * (1 / E))⁻¹) * u := by
    intro u
    field_simp
  simp only [hexp]
  have hlin : HasDerivAt (fun u : ℝ => (-(R * (1 / E))⁻¹) * u)
      ((-(R * (1 / E))⁻¹) * 1) t :=
    (hasDerivAt_id t).const_mul _
  have hexpD : HasDerivAt (fun u : ℝ => Real.exp ((-(R * (1 / E))⁻¹) * u))
      (Real.exp ((-(R * (1 / E))⁻¹) * t) * ((-(R * (1 / E))⁻¹) * 1)) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  have hmul := hexpD.const_mul (V0 - (1 / E) * dP)
  have hadd := hmul.const_add ((1 / E) * dP)
  have hder := hadd.deriv
  rw [hder]
  field_simp
  ring

/-- The respiratory response is the canonical one-compartment
amount with elimination rate `E / R` and input `dP / R`. -/
lemma respiratory_amount_eq {R E dP V0 : ℝ} (hR : 0 < R) (hE : 0 < E) :
    (fun t => (1 / E) * dP + (V0 - (1 / E) * dP) *
      Real.exp (-t / (R * (1 / E)))) =
    MathlibExt.Biology.Biophysics.CompartmentKinetics.amount
      (E / R) (dP / R) V0 := by
  funext t
  have hk : E / R ≠ 0 := div_ne_zero (ne_of_gt hE) (ne_of_gt hR)
  rw [MathlibExt.Biology.Biophysics.CompartmentKinetics.amount_eq_of_ne_zero hk]
  field_simp

/-- **Free expiration.** Zero drive: the response `V(t) = V0 * exp (-t / (R * C))`, `C = 1 / E`, solves the zero-drive equation `R V' + E V = 0` at every `t`. -/
lemma respiratory_expiration {R E V0 t : ℝ} (hR : 0 < R) (hE : 0 < E) :
    R * deriv (fun u => V0 * Real.exp (-u / (R * (1 / E)))) t +
      E * (V0 * Real.exp (-t / (R * (1 / E)))) = 0 := by
  have h := respiratory_response (R := R) (E := E) (dP := 0) (V0 := V0)
    (t := t) hR hE
  simpa using h

end PhyslibExt.Physiology.RespiratoryMechanics
