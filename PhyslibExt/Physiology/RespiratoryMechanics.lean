/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Respiratory mechanics agreement

The passive single-compartment equation `R V' + E V = Paw - P0`
with `R, E > 0` and compliance `C = 1/E` agrees with the scalar
evolution of decay `E/R`: the constant-drive closed form and free
expiration.
-/

@[expose] public section

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

/-- **Free expiration.** Zero drive: the response is the pure decay
`V0 * exp (-t / (R * C))` with `C = 1 / E`. -/
lemma respiratory_expiration {R E V0 t : ℝ} :
    (1 / E) * (0 : ℝ) + (V0 - (1 / E) * 0) * Real.exp (-t / (R * (1 / E))) =
      V0 * Real.exp (-t / (R * (1 / E))) := by
  simp

end PhyslibExt.Physiology.RespiratoryMechanics
