/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Sign.Basic
public import PhyslibExt.ContinuumMechanics.EngineeringScaling

/-!
# Range-guarded empirical heat-transfer correlations

A supplied Nusselt correlation is recorded with its formula, citation, and the flow configuration,
local/average tag and property-evaluation temperature it was calibrated with, and its nonempty
validity domain of flow conditions, and it is evaluated only for requests it applies to. For a
positive-coefficient power law `Nu = c Re ^ a Pr ^ b` at positive `Re` and `Pr`, the heat
transfer coefficient `h = Nu k / L` is positive and the convective heat rate `Q = h A ΔT` has the
sign of `ΔT`.

## i. Overview

* Request. A `CorrelationRequest` carries the complete application context in typed fields: the
  flow conditions (`Re`, `Pr`, the length ratio `L / D`, the surface-minus-fluid temperature
  difference `ΔT` and the bulk-to-surface viscosity ratio `μ_m / μ_s`), the flow configuration
  (`FlowConfiguration`: the geometry and flow arrangement, such as a smooth circular tube or a
  flat plate in parallel flow), the hydrodynamic and the thermal development at the evaluated
  section (each a `FlowDevelopment`: fully developed or in the entrance region of that
  profile), the size of the fluid-property variation caused by `ΔT` (`PropertyVariation`), the
  requested local or surface-averaged value, and the temperature at which the request's fluid
  properties were evaluated. The thermal direction is not a separate field:
  heating is `0 < ΔT` and cooling is `ΔT < 0` (`ThermalMode.Holds`), so it cannot disagree with
  the `ΔT` that drives the heat rate.
* Record. `NusseltCorrelation` stores the supplied formula, its citation (provenance only, not an
  applicability condition) and its typed applicability data. The validity domain
  is calibration evidence supplied with the correlation, not a proved fluid law; nothing here
  asserts that the formula is physically correct inside or outside it. A correlation with a
  length or thermal-direction condition puts it in the domain; one without such a condition
  leaves the field unconstrained. The formula reads only the flow conditions, so every input it
  needs is one of their fields: a large-property-variation correction of the Sieder-Tate type
  reads the viscosity ratio `μ_m / μ_s`, which a correlation for small to moderate property
  variation ignores.
* Guard. The formula field takes a proof that the flow conditions lie in the validity domain, so
  no out-of-domain value can be formed. `NusseltCorrelation.Applies C r` also requires the
  correlation's flow configuration, hydrodynamic and thermal development, property-variation
  class, local/average tag and property-evaluation temperature, and
  `NusseltCorrelation.nusselt` takes a proof of it; a correlation for another geometry, or for
  another development state of either profile, does not apply.
* Groups. `Re` and `Pr` are, for example, the dimensionless groups
  `EngineeringScaling.reynoldsNumber` and `EngineeringScaling.prandtlNumber`;
  `heatTransferCoefficient Nu k L = Nu k / L` inverts `EngineeringScaling.nusseltNumber`.
* Heat rate. `convectiveHeatRate h A ΔT = h A ΔT`, cast to the power dimension. Following the
  textbook reading, this relation defines `h`; it is a model input, not a derived heat-rate law.
  Through the guard, the heat rate uses the request's own `ΔT`.

Model inputs: the correlation, its validity domain and tags are supplied; `c, k, L, A > 0`; real
exponents with positive bases. No correlation is derived, no applicability range is invented, and
no empirical adequacy or system safety claim is made.

## ii. Key results

- `FlowConfiguration`, `FlowDevelopment`, `PropertyVariation`, `AveragingTag`,
  `PropertyTemperature`, `ThermalMode`, `ThermalMode.Holds`, `FlowConditions`,
  `CorrelationRequest` : the application context.
- `NusseltCorrelation`, `NusseltCorrelation.Applies`, `NusseltCorrelation.nusselt`,
  `NusseltCorrelation.exists_applies`, `powerLawCorrelation`, `powerLawCorrelation_nusselt` : the
  guarded interface.
- `NusseltCorrelation.applies_pos`, `reynoldsNumber_pos`, `prandtlNumber_pos`,
  `powerLaw_nusselt_pos` : positivity.
- `heatTransferCoefficient`, `heatTransferCoefficient_pos`, `nusseltNumber_heatTransferCoefficient`,
  `convectiveHeatRate`, `convectiveHeatRate_val`, `sign_convectiveHeatRate` : `h` and `Q`.
- `powerLaw_heatRate_sign`, `powerLawCorrelation_heatRate_sign` : the power-law chain, on the
  expression and through the guard.

## iii. Table of contents

- A. The application context and the guarded correlation record
- B. Heat transfer coefficient and heat rate

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, Wiley, chapters 6-8: Newton's law of cooling as the definition of `h`, the Nusselt
  number, local and average coefficients, property-evaluation temperatures (film temperature for
  external flow, mean temperature for internal flow), and the Dittus-Boelter correlation
  `Nu_D = 0.023 Re_D ^ (4/5) Pr ^ n` (`n = 0.4` for heating, `n = 0.3` for cooling) for fully
  developed turbulent flow in smooth circular tubes, `0.7 ≤ Pr ≤ 160`, `Re_D ≥ 10000`,
  `L / D ≥ 10`, small to moderate temperature differences `T_s - T_m`, properties at the mean
  temperature.
- ISO 80000-11, *Quantities and units — Part 11: Characteristic numbers*.
-/

@[expose] public section

open Dimension Units.QuantityDimensions Units.EngineeringQuantities EngineeringScaling

namespace CorrelationDomains

/-! ## A. The application context and the guarded correlation record -/

/-- The flow configuration a correlation was calibrated for: the geometry and the flow arrangement
around it. A correlation applies only to requests for its own configuration; a correlation for
another configuration needs its own constructor here. -/
inductive FlowConfiguration where
  /-- Internal flow through a smooth circular tube. -/
  | smoothCircularTube
  /-- External flow parallel to a flat plate. -/
  | flatPlateParallelFlow
  /-- External cross flow over a circular cylinder. -/
  | cylinderCrossFlow
  /-- External flow over a sphere. -/
  | sphere
  deriving DecidableEq

/-- The development of one profile at the evaluated section: the velocity profile
(hydrodynamic development) or the dimensionless temperature profile (thermal development).
Requests and correlations record the two separately, and a correlation applies only to requests
in its state for both. -/
inductive FlowDevelopment where
  /-- Fully developed: the profile no longer changes along the flow. -/
  | fullyDeveloped
  /-- In the entrance region of the profile. -/
  | developing
  deriving DecidableEq

/-- The size of the fluid-property variation across the boundary layer caused by the
surface-minus-fluid temperature difference. A correlation calibrated for one class applies only
to requests in that class. -/
inductive PropertyVariation where
  /-- Small to moderate temperature differences: properties evaluated at one reference
  temperature represent the flow. -/
  | smallToModerate
  /-- Large temperature differences, which need a property-ratio correction such as the wall
  viscosity factor `(μ_m / μ_s) ^ n`, read from `FlowConditions.viscosityRatio`. -/
  | large
  deriving DecidableEq

/-- Whether a correlation gives the local value at one surface position or the value averaged
over the surface. -/
inductive AveragingTag where
  | localValue
  | surfaceAverage
  deriving DecidableEq

/-- The fluid temperature at which the properties entering `Re`, `Pr` and `h = Nu k / L`
(viscosity, heat capacity, conductivity, density) are evaluated: the mean (bulk) temperature of a
duct flow, the film temperature `(T_s + T_∞) / 2` of an external flow, or the surface
temperature. A correlation is calibrated with one of them and applies only to requests whose
properties were evaluated at that temperature. -/
inductive PropertyTemperature where
  | bulkMean
  | film
  | surface
  deriving DecidableEq

/-- The thermal direction of a convection problem: the fluid is heated (the surface is warmer
than the fluid) or cooled. -/
inductive ThermalMode where
  | heating
  | cooling
  deriving DecidableEq

/-- The thermal direction `m` holds for the surface-minus-fluid temperature difference `ΔT`:
heating is `0 < ΔT` and cooling is `ΔT < 0`; at `ΔT = 0` neither holds. -/
def ThermalMode.Holds : ThermalMode → ℝ → Prop
  | .heating, ΔT => 0 < ΔT
  | .cooling, ΔT => ΔT < 0

/-- The flow conditions of a correlation request: the Reynolds and Prandtl numbers, the ratio
`L / D` of the heated length to the correlation's characteristic length (for a duct, its
diameter), the temperature difference `ΔT = T_s - T_m` between the surface and the reference
fluid temperature, which also drives the heat rate `Q = h A ΔT`, and the bulk-to-surface
viscosity ratio `μ_m / μ_s`. -/
structure FlowConditions where
  /-- The Reynolds number. -/
  reynolds : ℝ
  /-- The Prandtl number. -/
  prandtl : ℝ
  /-- The heated length over the characteristic length, `L / D`. -/
  lengthRatio : ℝ
  /-- The surface-minus-fluid temperature difference `T_s - T_m`. -/
  temperatureDifference : WithDim temperatureDim ℝ
  /-- The ratio `μ_m / μ_s` of the dynamic viscosity at the mean fluid temperature to the one at
  the surface temperature: the input of a Sieder-Tate-type property-ratio correction. -/
  viscosityRatio : ℝ

/-- A correlation request: its flow conditions, its flow configuration, the hydrodynamic and the
thermal development at the evaluated section, the property-variation class, the requested local
or surface-averaged value, and the temperature at which the request's fluid properties were
evaluated. -/
structure CorrelationRequest extends FlowConditions where
  /-- The geometry and flow arrangement of the request. -/
  configuration : FlowConfiguration
  /-- The development of the velocity profile at the evaluated section. -/
  hydrodynamicDevelopment : FlowDevelopment
  /-- The development of the dimensionless temperature profile at the evaluated section. -/
  thermalDevelopment : FlowDevelopment
  /-- The size of the fluid-property variation caused by the temperature difference. -/
  propertyVariation : PropertyVariation
  /-- Local or surface-averaged value requested. -/
  averaging : AveragingTag
  /-- The temperature at which the fluid properties in `Re`, `Pr` and `h` were evaluated. -/
  propertyTemperature : PropertyTemperature

/-- A supplied empirical Nusselt correlation: its citation, the flow configuration, hydrodynamic
and thermal development, property-variation class, local/average tag and property-evaluation
temperature it was calibrated with, its validity domain of flow conditions, which is nonempty
with positive `Re` and `Pr`, and its formula, which takes a proof that the flow conditions lie in
the domain. -/
structure NusseltCorrelation where
  /-- The published source of the correlation (provenance, not an applicability condition). -/
  citation : String
  /-- The geometry and flow arrangement the correlation was calibrated for. -/
  configuration : FlowConfiguration
  /-- The hydrodynamic development the correlation was calibrated for. -/
  hydrodynamicDevelopment : FlowDevelopment
  /-- The thermal development the correlation was calibrated for. -/
  thermalDevelopment : FlowDevelopment
  /-- The property-variation class the correlation was calibrated for. -/
  propertyVariation : PropertyVariation
  /-- Local or surface-averaged value. -/
  averaging : AveragingTag
  /-- The temperature at which the calibration evaluated the fluid properties. -/
  propertyTemperature : PropertyTemperature
  /-- The validity domain of flow conditions, supplied as calibration evidence. -/
  validity : Set FlowConditions
  validity_pos : ∀ s ∈ validity, 0 < s.reynolds ∧ 0 < s.prandtl
  validity_nonempty : validity.Nonempty
  /-- The supplied formula, defined only on the validity domain. -/
  formula : ∀ s ∈ validity, ℝ

/-- The correlation applies to a request: the request has the correlation's flow configuration,
hydrodynamic development, thermal development and property-variation class, asks for its
local/average value, its fluid properties were evaluated at the correlation's property
temperature, and its flow conditions lie in the validity domain. -/
def NusseltCorrelation.Applies (C : NusseltCorrelation) (r : CorrelationRequest) : Prop :=
  r.configuration = C.configuration ∧
    r.hydrodynamicDevelopment = C.hydrodynamicDevelopment ∧
    r.thermalDevelopment = C.thermalDevelopment ∧ r.propertyVariation = C.propertyVariation ∧
    r.averaging = C.averaging ∧ r.propertyTemperature = C.propertyTemperature ∧
    r.toFlowConditions ∈ C.validity

/-- The Nusselt number of the correlation for a request, evaluated only where the correlation
applies. -/
def NusseltCorrelation.nusselt (C : NusseltCorrelation) (r : CorrelationRequest)
    (h : C.Applies r) : ℝ :=
  C.formula r.toFlowConditions h.2.2.2.2.2.2

/-- Every correlation applies to some request: the guard is satisfiable. -/
lemma NusseltCorrelation.exists_applies (C : NusseltCorrelation) :
    ∃ r : CorrelationRequest, C.Applies r := by
  obtain ⟨s, hs⟩ := C.validity_nonempty
  exact ⟨⟨s, C.configuration, C.hydrodynamicDevelopment, C.thermalDevelopment,
    C.propertyVariation, C.averaging, C.propertyTemperature⟩, rfl, rfl, rfl, rfl, rfl, rfl, hs⟩

/-- The power-law correlation `Nu = c Re ^ a Pr ^ b` (real powers) with its citation, flow
configuration, hydrodynamic and thermal development, property-variation class, tags and validity
domain. -/
noncomputable def powerLawCorrelation (c a b : ℝ) (citation : String)
    (configuration : FlowConfiguration)
    (hydrodynamicDevelopment thermalDevelopment : FlowDevelopment)
    (propertyVariation : PropertyVariation) (averaging : AveragingTag)
    (propertyTemperature : PropertyTemperature)
    (validity : Set FlowConditions)
    (validity_pos : ∀ s ∈ validity, 0 < s.reynolds ∧ 0 < s.prandtl)
    (validity_nonempty : validity.Nonempty) : NusseltCorrelation where
  citation := citation
  configuration := configuration
  hydrodynamicDevelopment := hydrodynamicDevelopment
  thermalDevelopment := thermalDevelopment
  propertyVariation := propertyVariation
  averaging := averaging
  propertyTemperature := propertyTemperature
  validity := validity
  validity_pos := validity_pos
  validity_nonempty := validity_nonempty
  formula s _ := c * s.reynolds ^ a * s.prandtl ^ b

/-- Where the power-law correlation applies, it evaluates to `c Re ^ a Pr ^ b`. -/
lemma powerLawCorrelation_nusselt {c a b : ℝ} {citation : String}
    {configuration : FlowConfiguration}
    {hydrodynamicDevelopment thermalDevelopment : FlowDevelopment}
    {propertyVariation : PropertyVariation} {averaging : AveragingTag}
    {propertyTemperature : PropertyTemperature}
    {validity : Set FlowConditions}
    {validity_pos : ∀ s ∈ validity, 0 < s.reynolds ∧ 0 < s.prandtl}
    {validity_nonempty : validity.Nonempty} {r : CorrelationRequest}
    (h : (powerLawCorrelation c a b citation configuration hydrodynamicDevelopment
      thermalDevelopment propertyVariation averaging propertyTemperature validity validity_pos
      validity_nonempty).Applies r) :
    (powerLawCorrelation c a b citation configuration hydrodynamicDevelopment thermalDevelopment
      propertyVariation averaging propertyTemperature validity validity_pos
      validity_nonempty).nusselt r h =
      c * r.reynolds ^ a * r.prandtl ^ b :=
  rfl

/-- Where a correlation applies, `Re` and `Pr` are positive. -/
lemma NusseltCorrelation.applies_pos {C : NusseltCorrelation} {r : CorrelationRequest}
    (h : C.Applies r) : 0 < r.reynolds ∧ 0 < r.prandtl := by
  exact C.validity_pos _ h.2.2.2.2.2.2

/-- The Reynolds number of a positive density, a nonzero velocity and a positive length is
positive. -/
lemma reynoldsNumber_pos {ρ : WithDim massDensityDim ℝ} {U : WithDim velocityDim ℝ}
    {L : WithDim (single ISQDimensionBase.length) ℝ} {μ : WithDim dynamicViscosityDim ℝ}
    (hρ : 0 < ρ.val) (hU : U.val ≠ 0) (hL : 0 < L.val) (hμ : 0 < μ.val) :
    0 < reynoldsNumber ρ U L μ hμ := by
  rw [reynoldsNumber_val]
  exact div_pos (mul_pos (mul_pos hρ (abs_pos.mpr hU)) hL) hμ

/-- The Prandtl number of a positive viscosity and heat capacity is positive. -/
lemma prandtlNumber_pos {μ : WithDim dynamicViscosityDim ℝ}
    {cp : WithDim specificHeatCapacityDim ℝ} {k : WithDim thermalConductivityDim ℝ}
    (hμ : 0 < μ.val) (hcp : 0 < cp.val) (hk : 0 < k.val) :
    0 < prandtlNumber μ cp k hk := by
  rw [prandtlNumber_val]
  exact div_pos (mul_pos hμ hcp) hk

/-- A positive-coefficient power law is positive at positive `Re` and `Pr`, for all real
exponents. -/
lemma powerLaw_nusselt_pos {c a b Re Pr : ℝ} (hc : 0 < c) (hRe : 0 < Re) (hPr : 0 < Pr) :
    0 < c * Re ^ a * Pr ^ b := by
  exact mul_pos (mul_pos hc (Real.rpow_pos_of_pos hRe a)) (Real.rpow_pos_of_pos hPr b)

/-! ## B. Heat transfer coefficient and heat rate -/

/-- The heat transfer coefficient `h = Nu k / L` of a Nusselt number `Nu`, the fluid
conductivity `k` and a positive length `L`. -/
noncomputable def heatTransferCoefficient (Nu : ℝ) (k : WithDim thermalConductivityDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (_hL : 0 < L.val) :
    WithDim heatTransferCoefficientDim ℝ :=
  ⟨Nu * k.val / L.val⟩

/-- `h = Nu k / L` is positive for positive `Nu`, `k` and `L`. -/
lemma heatTransferCoefficient_pos {Nu : ℝ} {k : WithDim thermalConductivityDim ℝ}
    {L : WithDim (single ISQDimensionBase.length) ℝ} (hNu : 0 < Nu) (hk : 0 < k.val)
    (hL : 0 < L.val) : 0 < (heatTransferCoefficient Nu k L hL).val := by
  exact div_pos (mul_pos hNu hk) hL

/-- `h = Nu k / L` inverts the Nusselt group: `nusseltNumber h L k = Nu`. -/
lemma nusseltNumber_heatTransferCoefficient (Nu : ℝ) (k : WithDim thermalConductivityDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (hk : 0 < k.val) (hL : 0 < L.val) :
    nusseltNumber (heatTransferCoefficient Nu k L hL) L k hk = Nu := by
  rw [nusseltNumber_val]
  simp only [heatTransferCoefficient]
  field_simp

/-- The convective heat rate `Q = h A ΔT` into the fluid side, the defining relation of `h` (a
model input), cast to the power dimension. -/
noncomputable def convectiveHeatRate (h : WithDim heatTransferCoefficientDim ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ)
    (ΔT : WithDim temperatureDim ℝ) : WithDim powerDim ℝ :=
  WithDim.cast (h * A * ΔT) (by unfold heatTransferCoefficientDim temperatureDim; decide)

/-- `Q = h A ΔT` on coordinates. -/
lemma convectiveHeatRate_val (h : WithDim heatTransferCoefficientDim ℝ)
    (A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ) (ΔT : WithDim temperatureDim ℝ) :
    (convectiveHeatRate h A ΔT).val = h.val * A.val * ΔT.val := by
  rfl

/-- For positive `h` and `A`, the heat rate has the sign of `ΔT`. -/
lemma sign_convectiveHeatRate {h : WithDim heatTransferCoefficientDim ℝ}
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hh : 0 < h.val) (hA : 0 < A.val)
    (ΔT : WithDim temperatureDim ℝ) :
    SignType.sign (convectiveHeatRate h A ΔT).val = SignType.sign ΔT.val := by
  rw [convectiveHeatRate_val, sign_mul, sign_mul, sign_pos hh, sign_pos hA, one_mul, one_mul]

/-- The power-law chain: for `Nu = c Re ^ a Pr ^ b` with `c > 0` at positive `Re` and `Pr`, and
positive `k`, `L` and `A`, the coefficient `h = Nu k / L` is positive and `Q = h A ΔT` has the sign
of `ΔT`. -/
lemma powerLaw_heatRate_sign {c a b Re Pr : ℝ} (hc : 0 < c) (hRe : 0 < Re) (hPr : 0 < Pr)
    {k : WithDim thermalConductivityDim ℝ} {L : WithDim (single ISQDimensionBase.length) ℝ}
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hk : 0 < k.val) (hL : 0 < L.val)
    (hA : 0 < A.val) (ΔT : WithDim temperatureDim ℝ) :
    0 < (heatTransferCoefficient (c * Re ^ a * Pr ^ b) k L hL).val ∧
      SignType.sign
          (convectiveHeatRate (heatTransferCoefficient (c * Re ^ a * Pr ^ b) k L hL) A ΔT).val =
        SignType.sign ΔT.val := by
  have hNu := powerLaw_nusselt_pos (a := a) (b := b) hc hRe hPr
  have hh := heatTransferCoefficient_pos hNu hk hL
  exact ⟨hh, sign_convectiveHeatRate hh hA ΔT⟩

/-- The power-law chain through the guard: where a positive-coefficient power-law correlation
applies to a request, its Nusselt number gives a positive `h = Nu k / L`, and the heat rate
`Q = h A ΔT` at the request's own temperature difference has the sign of that difference. The
positivity of `Re` and `Pr` comes from the validity domain. -/
lemma powerLawCorrelation_heatRate_sign {c a b : ℝ} (hc : 0 < c) {citation : String}
    {configuration : FlowConfiguration}
    {hydrodynamicDevelopment thermalDevelopment : FlowDevelopment}
    {propertyVariation : PropertyVariation} {averaging : AveragingTag}
    {propertyTemperature : PropertyTemperature}
    {validity : Set FlowConditions}
    {validity_pos : ∀ s ∈ validity, 0 < s.reynolds ∧ 0 < s.prandtl}
    {validity_nonempty : validity.Nonempty} {r : CorrelationRequest}
    (h : (powerLawCorrelation c a b citation configuration hydrodynamicDevelopment
      thermalDevelopment propertyVariation averaging propertyTemperature validity validity_pos
      validity_nonempty).Applies r)
    {k : WithDim thermalConductivityDim ℝ} {L : WithDim (single ISQDimensionBase.length) ℝ}
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hk : 0 < k.val) (hL : 0 < L.val)
    (hA : 0 < A.val) :
    0 < (heatTransferCoefficient ((powerLawCorrelation c a b citation configuration
        hydrodynamicDevelopment thermalDevelopment propertyVariation averaging propertyTemperature
        validity validity_pos validity_nonempty).nusselt r h) k L hL).val ∧
      SignType.sign (convectiveHeatRate (heatTransferCoefficient ((powerLawCorrelation c a b
          citation configuration hydrodynamicDevelopment thermalDevelopment propertyVariation
          averaging propertyTemperature validity validity_pos validity_nonempty).nusselt r h)
          k L hL) A r.temperatureDifference).val =
        SignType.sign r.temperatureDifference.val := by
  have hRP := NusseltCorrelation.applies_pos h
  rw [powerLawCorrelation_nusselt h]
  exact powerLaw_heatRate_sign hc hRP.1 hRP.2 hk hL hA r.temperatureDifference

end CorrelationDomains
