/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.ContinuumMechanics.ControlVolumes
public import PhyslibExt.HeatTransfer.CorrelationDomains

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Guarded Darcy friction loss and its dissipated power

## i. Overview

A duct of length `L > 0`, hydraulic diameter `D > 0` and flow area `A > 0` carries a fluid of
density `ρ > 0` and viscosity `μ > 0` at the oriented volumetric flow `Q`, positive from the
inlet face to the outlet face. In the Darcy-Weisbach model the pressure drop from inlet to
outlet is `Δp = f (L / D) ρ V |V| / 2` with `V = Q / A`, that is `Δp = c Q |Q|` with the loss
coefficient `c = f L ρ / (2 D A ^ 2)`, where `f` is the Darcy friction factor.

* Request. A `FrictionRequest` carries the Reynolds number on the hydraulic diameter, the
  relative roughness `ε / D` of the wall (roughness height over hydraulic diameter, `0` for a
  smooth wall), the duct shape (`DuctShape`) and the hydrodynamic development at the evaluated
  section (`CorrelationDomains.FlowDevelopment`).
* Record. The factor comes from a supplied empirical correlation, guarded like the Nusselt
  correlations of `CorrelationDomains`: a `FrictionCorrelation` stores its citation, its
  friction-factor convention (Darcy `f_D` or Fanning `f_F = f_D / 4`), the duct shape,
  hydrodynamic development and relative roughness it was calibrated for, and its nonempty
  validity domain of positive Reynolds numbers; its formula takes a proof that the Reynolds
  number lies in the domain. `FrictionCorrelation.DarcyApplies C r` also requires the Darcy
  convention and the request's duct shape, development and relative roughness, compared by
  equality, and `FrictionCorrelation.darcyFactor` takes a proof of it. No value is formed outside
  the validity box or for another roughness, and a Fanning record cannot be read as a Darcy
  factor. A correlation that reads the roughness, such as a Colebrook-type formula, is recorded
  once per relative roughness, with that roughness in its formula.
* Coefficient. For one positive Darcy factor `f` read through the guard at a request whose
  Reynolds number and relative roughness are those of the flow and the pipe,
  `Re = ρ |Q / A| D / μ` (`EngineeringScaling.reynoldsNumber`, the speed `|V|`) and `ε / D`, the
  correlation was calibrated for the pipe's roughness and the coefficient `c` is positive.
* Power and reversal. `Δp Q = c Q ^ 2 |Q| ≥ 0`, positive for `Q ≠ 0`; `Δp` has the sign of `Q`
  and changes sign with it. The reversed flow `-Q` has the same speed, hence the same Reynolds
  number, in the same pipe, hence the same roughness, so the same certified factor applies to
  it, and the pressure drop `-Δp`.
* Energy ports. In a steady duct segment without heat or shaft work whose two ports have the
  same area, density, velocity and elevation, the outward port energy rates of
  `ControlVolumes.portEnergyRate` (flow work counted once) sum to zero exactly when the
  internal-energy rise carried by the mass flow `ρ A V` equals the pressure-drop power
  `(p_in - p_out) A V`; with the Darcy loss it is `c Q ^ 2 |Q| ≥ 0`.

Model inputs: the correlation, its convention, roughness, validity domain and tags are supplied,
and one positive factor value is assumed, not proved; the Darcy-Weisbach relation is the
specified coefficient model. No monotonicity of the factor in `Re` is assumed, no correlation is
validated, and no empirical adequacy or system safety claim is made.

## ii. Key results

- `FluidDynamics.PipeFrictionPorts.DuctShape`, `FrictionRequest`: the request data.
- `FluidDynamics.PipeFrictionPorts.FrictionCorrelation`, `FrictionCorrelation.DarcyApplies`,
  `FrictionCorrelation.darcyFactor`, `FrictionCorrelation.not_darcyApplies`: the guarded record.
- `FluidDynamics.PipeFrictionPorts.powerLawFriction`, `powerLawFriction_darcyFactor`,
  `powerLawFriction_darcyFactor_pos`: power-law friction correlations.
- `FluidDynamics.PipeFrictionPorts.darcyWeisbach_eq`, `darcyCoefficient_pos`:
  `Δp = c Q |Q|`, `c > 0`.
- `FluidDynamics.PipeFrictionPorts.frictionPressureDrop_neg`, `sign_frictionPressureDrop`:
  reversal and sign.
- `FluidDynamics.PipeFrictionPorts.dissipatedPower_nonneg`, `dissipatedPower_pos`: the
  dissipated power.
- `FluidDynamics.PipeFrictionPorts.dissipatedPower_eq_internalEnergyRise`,
  `internalEnergyRise_frictionPressureDrop`: the power through the energy ports.
- `FluidDynamics.PipeFrictionPorts.darcyFactor_frictionPressureDrop`: the guarded chain.

## iii. Table of contents

- A. A guarded friction-factor record
- B. The Darcy-Weisbach loss and its dissipated power
- C. Dissipated power through the energy ports
- D. The guarded loss

## iv. References

- F. M. White, *Fluid Mechanics*, McGraw-Hill, chapter 6: the Darcy-Weisbach head loss
  `h_f = f (L / d) V ^ 2 / (2 g)`, the Darcy and Fanning friction factors (`f_D = 4 f_F`), and
  the Blasius smooth-pipe law `f ≈ 0.316 Re_d ^ (-1/4)` for `4000 < Re_d < 100000`.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, Wiley, chapter 8: the Moody (Darcy) friction factor and the pressure drop of fully
  developed internal flow.
- `PhyslibExt.HeatTransfer.CorrelationDomains` (the flow-development type and the guard
  pattern) and
  `ControlVolumes.portEnergyRate` (`PhyslibExt.ContinuumMechanics.ControlVolumes`).
-/

@[expose] public section

open CorrelationDomains EngineeringScaling

namespace FluidDynamics.PipeFrictionPorts

/-! ## A. A guarded friction-factor record -/

/-- The friction-factor convention of a correlation: the Darcy (Moody) factor `f_D` of
`Δp = f_D (L / D) ρ V ^ 2 / 2`, or the Fanning factor `f_F = f_D / 4` of the wall shear stress
`τ_w = f_F ρ V ^ 2 / 2`. -/
inductive FrictionConvention where
  | darcy
  | fanning
  deriving DecidableEq

/-- The duct shape a friction correlation was calibrated for: a circular tube, whose hydraulic
diameter is its diameter, or a noncircular duct described by its hydraulic diameter. The wall
roughness is a separate request field; `CorrelationDomains.FlowConfiguration` is not reused here
because its tube constructor fixes a smooth wall. -/
inductive DuctShape where
  /-- A circular tube. -/
  | circularTube
  /-- A noncircular duct, described by its hydraulic diameter. -/
  | noncircularDuct
  deriving DecidableEq

/-- A friction-factor request: the Reynolds number `Re = ρ |V| D / μ` on the hydraulic diameter
`D`, the relative roughness `ε / D` of the duct wall (roughness height `ε` over `D`, `0` for a
smooth wall), the duct shape, and the hydrodynamic development at the evaluated section. -/
structure FrictionRequest where
  /-- The Reynolds number on the hydraulic diameter. -/
  reynolds : ℝ
  /-- The relative roughness `ε / D` of the duct wall, `0` for a smooth wall. -/
  relativeRoughness : ℝ
  /-- The duct shape. -/
  ductShape : DuctShape
  /-- The development of the velocity profile at the evaluated section. -/
  hydrodynamicDevelopment : FlowDevelopment

/-- A supplied empirical friction-factor correlation: its citation, its convention, the duct
shape, hydrodynamic development and wall relative roughness it was calibrated for, its validity
domain of Reynolds numbers, which is nonempty and positive, and its formula, which takes a proof
that the Reynolds number lies in the domain. A correlation that reads the roughness, such as a
Colebrook-type formula, is recorded once per relative roughness, with that roughness in its
formula. -/
structure FrictionCorrelation where
  /-- The published source of the correlation (provenance, not an applicability condition). -/
  citation : String
  /-- The friction-factor convention of the formula. -/
  convention : FrictionConvention
  /-- The duct shape the correlation was calibrated for. -/
  ductShape : DuctShape
  /-- The hydrodynamic development the correlation was calibrated for. -/
  hydrodynamicDevelopment : FlowDevelopment
  /-- The relative roughness `ε / D` the correlation was calibrated for, `0` for a smooth wall. -/
  relativeRoughness : ℝ
  /-- The validity domain of Reynolds numbers, supplied as calibration evidence. -/
  validity : Set ℝ
  validity_pos : ∀ Re ∈ validity, 0 < Re
  validity_nonempty : validity.Nonempty
  /-- The supplied formula, defined only on the validity domain. -/
  formula : ∀ Re ∈ validity, ℝ

/-- The correlation supplies a Darcy factor for a request: it is in the Darcy convention, the
request has its duct shape, hydrodynamic development and relative roughness (each compared by
equality), and the request's Reynolds number lies in its validity domain. -/
def FrictionCorrelation.DarcyApplies (C : FrictionCorrelation) (r : FrictionRequest) : Prop :=
  C.convention = FrictionConvention.darcy ∧ r.ductShape = C.ductShape ∧
    r.hydrodynamicDevelopment = C.hydrodynamicDevelopment ∧
    r.relativeRoughness = C.relativeRoughness ∧ r.reynolds ∈ C.validity

/-- The Darcy factor of the correlation for a request, evaluated only where it applies. -/
def FrictionCorrelation.darcyFactor (C : FrictionCorrelation) (r : FrictionRequest)
    (h : C.DarcyApplies r) : ℝ :=
  C.formula r.reynolds h.2.2.2.2

/-- **No value outside the box.** A Fanning record, a request with another relative roughness, or
a request outside the validity domain gives no Darcy factor. -/
lemma FrictionCorrelation.not_darcyApplies {C : FrictionCorrelation} {r : FrictionRequest}
    (h : C.convention = FrictionConvention.fanning ∨ r.relativeRoughness ≠ C.relativeRoughness ∨
      r.reynolds ∉ C.validity) :
    ¬ C.DarcyApplies r := by
  rintro ⟨hc, -, -, hε, hv⟩
  rcases h with h | h | h
  · rw [hc] at h
    exact absurd h (by decide)
  · exact h hε
  · exact h hv

/-- The power-law friction correlation `f = c Re ^ a` (real power) with its citation, convention,
duct shape, hydrodynamic development, relative roughness and validity domain. -/
noncomputable def powerLawFriction (c a : ℝ) (citation : String)
    (convention : FrictionConvention) (ductShape : DuctShape)
    (hydrodynamicDevelopment : FlowDevelopment) (relativeRoughness : ℝ) (validity : Set ℝ)
    (validity_pos : ∀ Re ∈ validity, 0 < Re) (validity_nonempty : validity.Nonempty) :
    FrictionCorrelation where
  citation := citation
  convention := convention
  ductShape := ductShape
  hydrodynamicDevelopment := hydrodynamicDevelopment
  relativeRoughness := relativeRoughness
  validity := validity
  validity_pos := validity_pos
  validity_nonempty := validity_nonempty
  formula Re _ := c * Re ^ a

/-- Where a power-law friction correlation applies, its Darcy factor is `c Re ^ a`. -/
lemma powerLawFriction_darcyFactor {c a : ℝ} {citation : String}
    {convention : FrictionConvention} {ductShape : DuctShape}
    {hydrodynamicDevelopment : FlowDevelopment} {relativeRoughness : ℝ} {validity : Set ℝ}
    {validity_pos : ∀ Re ∈ validity, 0 < Re} {validity_nonempty : validity.Nonempty}
    {r : FrictionRequest}
    (h : (powerLawFriction c a citation convention ductShape hydrodynamicDevelopment
      relativeRoughness validity validity_pos validity_nonempty).DarcyApplies r) :
    (powerLawFriction c a citation convention ductShape hydrodynamicDevelopment relativeRoughness
      validity validity_pos validity_nonempty).darcyFactor r h = c * r.reynolds ^ a := by
  rfl

/-- A positive-coefficient power-law correlation gives a positive Darcy factor where it applies,
for every real exponent: the validity domain makes `Re` positive. -/
lemma powerLawFriction_darcyFactor_pos {c a : ℝ} (hc : 0 < c) {citation : String}
    {convention : FrictionConvention} {ductShape : DuctShape}
    {hydrodynamicDevelopment : FlowDevelopment} {relativeRoughness : ℝ} {validity : Set ℝ}
    {validity_pos : ∀ Re ∈ validity, 0 < Re} {validity_nonempty : validity.Nonempty}
    {r : FrictionRequest}
    (h : (powerLawFriction c a citation convention ductShape hydrodynamicDevelopment
      relativeRoughness validity validity_pos validity_nonempty).DarcyApplies r) :
    0 < (powerLawFriction c a citation convention ductShape hydrodynamicDevelopment
      relativeRoughness validity validity_pos validity_nonempty).darcyFactor r h := by
  rw [powerLawFriction_darcyFactor h]
  exact mul_pos hc (Real.rpow_pos_of_pos (validity_pos _ h.2.2.2.2) a)

/-! ## B. The Darcy-Weisbach loss and its dissipated power -/

/-- The Darcy-Weisbach loss coefficient `c = f L ρ / (2 D A ^ 2)` of a duct of length `L`,
hydraulic diameter `D` and flow area `A` carrying a fluid of density `ρ`, for the Darcy factor
`f`. -/
noncomputable def darcyCoefficient (f L D A ρ : ℝ) : ℝ := f * L * ρ / (2 * D * A ^ 2)

/-- The oriented pressure drop `Δp = c Q |Q|` from the inlet to the outlet face at the
volumetric flow `Q`, positive from inlet to outlet. -/
noncomputable def frictionPressureDrop (c Q : ℝ) : ℝ := c * Q * |Q|

/-- **Darcy-Weisbach in flow form.** For `D ≠ 0` and `A > 0`, the pressure drop
`f (L / D) ρ V |V| / 2` at the mean velocity `V = Q / A` is `c Q |Q|` with
`c = f L ρ / (2 D A ^ 2)`. -/
lemma darcyWeisbach_eq {f L D A ρ : ℝ} (hD : D ≠ 0) (hA : 0 < A) (Q : ℝ) :
    f * (L / D) * (ρ * (Q / A) * |Q / A| / 2) =
      frictionPressureDrop (darcyCoefficient f L D A ρ) Q := by
  unfold frictionPressureDrop darcyCoefficient
  rw [abs_div, abs_of_pos hA]
  field_simp

/-- The loss coefficient of a positive factor, length, diameter, area and density is
positive. -/
lemma darcyCoefficient_pos {f L D A ρ : ℝ} (hf : 0 < f) (hL : 0 < L) (hD : 0 < D) (hA : 0 < A)
    (hρ : 0 < ρ) : 0 < darcyCoefficient f L D A ρ := by
  unfold darcyCoefficient
  positivity

/-- **Flow reversal** reverses the pressure drop: `Δp(-Q) = -Δp(Q)`. -/
lemma frictionPressureDrop_neg (c Q : ℝ) :
    frictionPressureDrop c (-Q) = -frictionPressureDrop c Q := by
  unfold frictionPressureDrop
  rw [abs_neg]
  ring

/-- For `c > 0` the pressure drop has the sign of the flow. -/
lemma sign_frictionPressureDrop {c : ℝ} (hc : 0 < c) (Q : ℝ) :
    SignType.sign (frictionPressureDrop c Q) = SignType.sign Q := by
  unfold frictionPressureDrop
  by_cases hQ : Q = 0
  · simp [hQ]
  · rw [sign_mul, sign_mul, sign_pos hc, sign_pos (abs_pos.mpr hQ), one_mul, mul_one]

/-- **Nonnegative dissipated power.** For `c ≥ 0`, `Δp Q = c Q ^ 2 |Q| ≥ 0`. -/
lemma dissipatedPower_nonneg {c : ℝ} (hc : 0 ≤ c) (Q : ℝ) :
    frictionPressureDrop c Q * Q = c * Q ^ 2 * |Q| ∧ 0 ≤ frictionPressureDrop c Q * Q := by
  unfold frictionPressureDrop
  refine ⟨by ring, ?_⟩
  have h : c * Q * |Q| * Q = c * Q ^ 2 * |Q| := by ring
  rw [h]
  exact mul_nonneg (mul_nonneg hc (sq_nonneg Q)) (abs_nonneg Q)

/-- For `c > 0` every nonzero flow, forward or reverse, dissipates a positive power. -/
lemma dissipatedPower_pos {c Q : ℝ} (hc : 0 < c) (hQ : Q ≠ 0) :
    0 < frictionPressureDrop c Q * Q := by
  unfold frictionPressureDrop
  have h : c * Q * |Q| * Q = c * Q ^ 2 * |Q| := by ring
  rw [h]
  exact mul_pos (mul_pos hc (pow_pos (abs_pos.mpr hQ) 2 |>.trans_eq (sq_abs Q))) (abs_pos.mpr hQ)

/-! ## C. Dissipated power through the energy ports -/

/-- **The dissipated power is the internal-energy rise.** A duct segment with inlet and outlet
faces of area `A`, density `ρ`, the same port velocity `v` with axial component `V` (outward
normal velocity `V` at the outlet and `-V` at the inlet) and the same elevation `z`, in a steady
state without heat or shaft work: its outward port energy rates, with the flow work counted once,
sum to zero. Then the internal-energy rise carried by the mass flow `ρ A V` equals the
pressure-drop power `(p_in - p_out) A V`. -/
lemma dissipatedPower_eq_internalEnergyRise {m : ℕ} {ρ A V ein eout pin pout g z : ℝ}
    (v : Fin m → ℝ)
    (hbal : ControlVolumes.portEnergyRate ρ A V eout pout g z v +
      ControlVolumes.portEnergyRate ρ A (-V) ein pin g z v = 0) :
    ρ * (A * V) * (eout - ein) = (pin - pout) * (A * V) := by
  unfold ControlVolumes.portEnergyRate at hbal
  linear_combination hbal

/-- With the Darcy loss `p_in - p_out = c Q |Q|` at `Q = A V` and `c ≥ 0`, the internal-energy
rise of the steady segment is `c Q ^ 2 |Q| ≥ 0`, in both flow directions. -/
lemma internalEnergyRise_frictionPressureDrop {m : ℕ} {ρ A V ein eout pin pout g z c : ℝ}
    (v : Fin m → ℝ)
    (hbal : ControlVolumes.portEnergyRate ρ A V eout pout g z v +
      ControlVolumes.portEnergyRate ρ A (-V) ein pin g z v = 0)
    (hΔp : pin - pout = frictionPressureDrop c (A * V)) (hc : 0 ≤ c) :
    ρ * (A * V) * (eout - ein) = c * (A * V) ^ 2 * |A * V| ∧
      0 ≤ ρ * (A * V) * (eout - ein) := by
  rw [dissipatedPower_eq_internalEnergyRise v hbal, hΔp]
  exact dissipatedPower_nonneg hc (A * V)

/-! ## D. The guarded loss -/

/-- **Guarded friction loss.** Where a friction correlation supplies a Darcy factor `f > 0` for a
request whose Reynolds number and relative roughness are those of the flow and the pipe,
`Re = ρ |Q / A| D / μ` and `ε / D`, the correlation was calibrated for the pipe's relative
roughness; the coefficient `c = f L ρ / (2 D A ^ 2)` is positive; the reversed flow `-Q` has the
same Reynolds number (and, in the same pipe, the same roughness), so the same certified factor
applies to it; the dissipated power `Δp Q` is nonnegative; and the reversed flow has the pressure
drop `-Δp`. -/
lemma darcyFactor_frictionPressureDrop {C : FrictionCorrelation} {r : FrictionRequest}
    (h : C.DarcyApplies r) (hf : 0 < C.darcyFactor r h) {L D A ρ μ Q ε : ℝ} (hL : 0 < L)
    (hD : 0 < D) (hA : 0 < A) (hρ : 0 < ρ) (hμ : 0 < μ)
    (hRe : r.reynolds = reynoldsNumber ⟨ρ⟩ ⟨Q / A⟩ ⟨D⟩ ⟨μ⟩ hμ)
    (hε : r.relativeRoughness = ε / D) :
    C.relativeRoughness = ε / D ∧
      0 < darcyCoefficient (C.darcyFactor r h) L D A ρ ∧
      r.reynolds = reynoldsNumber ⟨ρ⟩ ⟨-Q / A⟩ ⟨D⟩ ⟨μ⟩ hμ ∧
      0 ≤ frictionPressureDrop (darcyCoefficient (C.darcyFactor r h) L D A ρ) Q * Q ∧
      frictionPressureDrop (darcyCoefficient (C.darcyFactor r h) L D A ρ) (-Q) =
        -frictionPressureDrop (darcyCoefficient (C.darcyFactor r h) L D A ρ) Q := by
  have hc := darcyCoefficient_pos hf hL hD hA hρ
  refine ⟨h.2.2.2.1.symm.trans hε, hc, ?_, (dissipatedPower_nonneg hc.le Q).2,
    frictionPressureDrop_neg _ Q⟩
  rw [hRe, reynoldsNumber_val, reynoldsNumber_val]
  simp only [neg_div, abs_neg]

end FluidDynamics.PipeFrictionPorts
