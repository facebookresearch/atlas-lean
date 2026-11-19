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

A supplied Nusselt correlation `Nu = f(Re, Pr)` is recorded with its formula, citation, geometry,
property-evaluation temperature, local/average tag and its positive, nonempty validity domain in
the `(Re, Pr)` plane, and it is evaluated only where it applies. For a positive-coefficient power
law `Nu = c Re ^ a Pr ^ b` at positive `Re` and `Pr`, the heat transfer coefficient
`h = Nu k / L` is positive and the convective heat rate `Q = h A ΔT` has the sign of `ΔT`.

## i. Overview

* Record. `NusseltCorrelation` stores the supplied formula and its provenance. The validity domain
  is calibration evidence supplied with the correlation, not a proved fluid law; nothing here
  asserts that the formula is physically correct inside or outside it.
* Guard. The formula field takes a proof that `(Re, Pr)` lies in the validity domain, so no
  out-of-domain value can be formed. `NusseltCorrelation.Applies C tag Re Pr` adds the requested
  local/average tag; `NusseltCorrelation.nusselt` takes a proof of it, so a local/average
  mismatch cannot be evaluated either.
* Groups. `Re` and `Pr` are the dimensionless groups `EngineeringScaling.reynoldsNumber` and
  `EngineeringScaling.prandtlNumber`; `heatTransferCoefficient Nu k L = Nu k / L` inverts
  `EngineeringScaling.nusseltNumber`.
* Heat rate. `convectiveHeatRate h A ΔT = h A ΔT`, cast to the power dimension. Following the
  textbook reading, this relation defines `h`; it is a model input, not a derived heat-rate law.

Model inputs: the correlation, its validity domain and tags are supplied; `c, k, L, A > 0`; real
exponents with positive bases. No correlation is derived, no applicability range is invented, and
no empirical adequacy or system safety claim is made.

## ii. Key results

- `AveragingTag`, `NusseltCorrelation`, `NusseltCorrelation.Applies`,
  `NusseltCorrelation.nusselt`, `powerLawCorrelation` : the guarded interface.
- `NusseltCorrelation.applies_pos`, `reynoldsNumber_pos`, `prandtlNumber_pos`,
  `powerLaw_nusselt_pos` : positivity.
- `heatTransferCoefficient`, `heatTransferCoefficient_pos`, `nusseltNumber_heatTransferCoefficient`,
  `convectiveHeatRate`, `convectiveHeatRate_val`, `sign_convectiveHeatRate` : `h` and `Q`.
- `powerLaw_heatRate_sign`, `powerLawCorrelation_nusselt`, `powerLawCorrelation_heatRate_sign` :
  the power-law chain, on the expression and through the guard.

## iii. Table of contents

- A. The guarded correlation record
- B. Heat transfer coefficient and heat rate

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, Wiley, chapters 6-8: Newton's law of cooling as the definition of `h`, the Nusselt
  number, local and average coefficients, property-evaluation temperatures, and the
  Dittus-Boelter correlation `Nu_D = 0.023 Re_D ^ (4/5) Pr ^ n` (`n = 0.4` for heating) for fully
  developed turbulent flow in smooth circular tubes, `0.6 ≤ Pr ≤ 160`, `Re_D ≥ 10000`,
  `L / D ≥ 10`.
- ISO 80000-11, *Quantities and units — Part 11: Characteristic numbers*.
-/

@[expose] public section

open Dimension Units.QuantityDimensions Units.EngineeringQuantities EngineeringScaling

namespace CorrelationDomains

/-! ## A. The guarded correlation record -/

/-- Whether a correlation gives the local value at one surface position or the value averaged
over the surface. -/
inductive AveragingTag where
  | localValue
  | surfaceAverage
  deriving DecidableEq

/-- A supplied empirical Nusselt correlation with its citation, geometry, property-evaluation
temperature, local/average tag, validity domain in the `(Re, Pr)` plane, which is positive and
nonempty, and its formula `Nu = formula (Re, Pr) h`, which takes a proof `h` that `(Re, Pr)` lies
in the domain. -/
structure NusseltCorrelation where
  /-- The published source of the correlation. -/
  citation : String
  /-- The geometry and flow configuration the correlation was calibrated for. -/
  geometry : String
  /-- The temperature at which the fluid properties are evaluated. -/
  propertyTemperature : String
  /-- Local or surface-averaged value. -/
  averaging : AveragingTag
  /-- The validity domain of `(Re, Pr)`, supplied as calibration evidence. -/
  validity : Set (ℝ × ℝ)
  validity_pos : ∀ p ∈ validity, 0 < p.1 ∧ 0 < p.2
  validity_nonempty : validity.Nonempty
  /-- The supplied formula, defined only on the validity domain. -/
  formula : ∀ p ∈ validity, ℝ

/-- The correlation applies to a request for a `tag` value at `(Re, Pr)`: the tags agree and
`(Re, Pr)` lies in the validity domain. -/
def NusseltCorrelation.Applies (C : NusseltCorrelation) (tag : AveragingTag) (Re Pr : ℝ) :
    Prop :=
  C.averaging = tag ∧ (Re, Pr) ∈ C.validity

/-- The Nusselt number of the correlation for a request with tag `tag` at `(Re, Pr)`, evaluated
only where the correlation applies. -/
def NusseltCorrelation.nusselt (C : NusseltCorrelation) (tag : AveragingTag) (Re Pr : ℝ)
    (h : C.Applies tag Re Pr) : ℝ :=
  C.formula (Re, Pr) h.2

/-- The power-law correlation `Nu = c Re ^ a Pr ^ b` (real powers) with its recorded provenance
and validity domain. -/
noncomputable def powerLawCorrelation (c a b : ℝ) (citation geometry propertyTemperature : String)
    (averaging : AveragingTag) (validity : Set (ℝ × ℝ))
    (validity_pos : ∀ p ∈ validity, 0 < p.1 ∧ 0 < p.2) (validity_nonempty : validity.Nonempty) :
    NusseltCorrelation where
  citation := citation
  geometry := geometry
  propertyTemperature := propertyTemperature
  averaging := averaging
  validity := validity
  validity_pos := validity_pos
  validity_nonempty := validity_nonempty
  formula p _ := c * p.1 ^ a * p.2 ^ b

/-- Where the power-law correlation applies, it evaluates to `c Re ^ a Pr ^ b`. -/
lemma powerLawCorrelation_nusselt {c a b : ℝ} {citation geometry propertyTemperature : String}
    {averaging : AveragingTag} {validity : Set (ℝ × ℝ)}
    {validity_pos : ∀ p ∈ validity, 0 < p.1 ∧ 0 < p.2} {validity_nonempty : validity.Nonempty}
    {tag : AveragingTag} {Re Pr : ℝ}
    (h : (powerLawCorrelation c a b citation geometry propertyTemperature averaging validity
      validity_pos validity_nonempty).Applies tag Re Pr) :
    (powerLawCorrelation c a b citation geometry propertyTemperature averaging validity
      validity_pos validity_nonempty).nusselt tag Re Pr h = c * Re ^ a * Pr ^ b :=
  rfl

/-- Where a correlation applies, `Re` and `Pr` are positive. -/
lemma NusseltCorrelation.applies_pos {C : NusseltCorrelation} {tag : AveragingTag} {Re Pr : ℝ}
    (h : C.Applies tag Re Pr) : 0 < Re ∧ 0 < Pr := by
  exact C.validity_pos _ h.2

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
applies, its Nusselt number gives a positive `h = Nu k / L`, and `Q = h A ΔT` has the sign of `ΔT`.
The positivity of `Re` and `Pr` comes from the validity domain. -/
lemma powerLawCorrelation_heatRate_sign {c a b : ℝ} (hc : 0 < c)
    {citation geometry propertyTemperature : String} {averaging : AveragingTag}
    {validity : Set (ℝ × ℝ)} {validity_pos : ∀ p ∈ validity, 0 < p.1 ∧ 0 < p.2}
    {validity_nonempty : validity.Nonempty} {tag : AveragingTag} {Re Pr : ℝ}
    (h : (powerLawCorrelation c a b citation geometry propertyTemperature averaging validity
      validity_pos validity_nonempty).Applies tag Re Pr)
    {k : WithDim thermalConductivityDim ℝ} {L : WithDim (single ISQDimensionBase.length) ℝ}
    {A : WithDim (single ISQDimensionBase.length ^ (2 : ℕ)) ℝ} (hk : 0 < k.val) (hL : 0 < L.val)
    (hA : 0 < A.val) (ΔT : WithDim temperatureDim ℝ) :
    0 < (heatTransferCoefficient ((powerLawCorrelation c a b citation geometry
        propertyTemperature averaging validity validity_pos validity_nonempty).nusselt tag Re Pr h)
        k L hL).val ∧
      SignType.sign (convectiveHeatRate (heatTransferCoefficient ((powerLawCorrelation c a b
          citation geometry propertyTemperature averaging validity validity_pos
          validity_nonempty).nusselt tag Re Pr h) k L hL) A ΔT).val =
        SignType.sign ΔT.val := by
  have hRP := NusseltCorrelation.applies_pos h
  rw [powerLawCorrelation_nusselt h]
  exact powerLaw_heatRate_sign hc hRP.1 hRP.2 hk hL hA ΔT

end CorrelationDomains
