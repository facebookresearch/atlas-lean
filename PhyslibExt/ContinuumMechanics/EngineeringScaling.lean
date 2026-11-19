/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Units.EngineeringQuantities

/-!
# Engineering dimensionless groups

The Reynolds, Prandtl, Nusselt, Rayleigh, Mach, Froude and Biot numbers, each written once over
typed ISQ quantities, with their dimension identities and their invariance under every change
of unit scale.

## i. Overview

Each group takes its physical inputs as `WithDim d ℝ` quantities over Physlib's seven-base
`ISQDimensionBase`, so every symbol carries its declared dimension in its type. Except for the
Froude number, a group is the coordinate of the `WithDim` monomial cast to `dimensionlessDim`;
the cast is the dimension identity, checked when the definition elaborates. A positivity
hypothesis on every denominator is part of each definition, as for `logRatio` and
`expScaledEnergy` in `PhyslibExt.Units.QuantityDimensions`.

* `Re = ρ |U| L / μ`, `Pr = μ c_p / k`, `Nu = h L / k`, `Ra = |g| β ΔT L ^ 3 / (ν κ)`,
  `Ma = |U| / a`, `Fr = |U| / √(g L)` and `Bi = h L / k_s`. As in ISO 80000-11, the Reynolds,
  Mach and Froude numbers use the speed `|U|` of the signed velocity coordinate `U`, and the
  Rayleigh number uses the magnitude `|g|` of the gravitational acceleration; `ΔT` keeps its
  sign.
* `c_p` is a mass-specific heat capacity `L² T⁻² Θ⁻¹`. A molar heat capacity has the dimension
  `gasConstantDim` of the molar gas constant, so it is a different type and cannot be passed to
  `prandtlNumber`; it must first be divided by a molar mass.
* `ν` and `κ` both have the existing `diffusivityDim` `L² T⁻¹`, `β` has `Θ⁻¹`, and `ΔT` is a
  temperature difference of dimension `Θ`. Celsius and kelvin differences agree, while a Celsius
  reading is affine and is not a coordinate of any `UnitScale`.
* The Nusselt and Biot numbers are the same monomial `h L / k`; the dimension does not record
  whether `k` is the conductivity of the fluid (`Nu`) or of the solid (`Bi`).
* The Froude number takes a real square root, which has no `WithDim` counterpart; it is defined
  on coordinates, and its dimension identity is stated with the exponent `1 / 2`.

Unit invariance is the statement that rescaling every input by the `UnitScale.dimScale` factor
of its own dimension does not change the group. It follows from the existing `dimScale_mul`
and `dimScale_pos`; no new rescaling theorem is introduced. The power dimension `powerDim` and
the fixture scales `siScale` and `mmScale` are reused from
`PhyslibExt.Units.EngineeringQuantities`.

Model inputs (hypotheses):

* the basis is the seven-base ISQ, and unit choices are `UnitScale`s;
* each input has its declared dimension, `c_p` is mass-specific, and every denominator is
  positive (`g L > 0` for the Froude number).

Non-goals: these are dimensional identities only. No similarity law, no transfer of an
empirical correlation between flows, no Buckingham π theorem (whose counting form lives in
`PhyslibExt.Chemistry.QuantityCalculus`), and no empirical adequacy or system safety claim.

## ii. Key results

- `velocityDim_exponent`, `accelerationDim_exponent`, `massDensityDim_exponent`,
  `dynamicViscosityDim_exponent`, `specificHeatCapacityDim_exponent`,
  `thermalConductivityDim_exponent`, `heatTransferCoefficientDim_exponent` : the exponent
  vectors of the new dimension names.
- `reynoldsNumber_dimensionless`, `prandtlNumber_dimensionless`,
  `nusseltNumber_dimensionless`, `rayleighNumber_dimensionless`,
  `froudeNumber_dimensionless` : the dimension identities.
- `reynoldsNumber_val`, `prandtlNumber_val`, `nusseltNumber_val`, `rayleighNumber_val`,
  `machNumber_val`, `biotNumber_val` : the coordinate formulas.
- `reynoldsNumber_dimScale`, `prandtlNumber_dimScale`, `nusseltNumber_dimScale`,
  `rayleighNumber_dimScale`, `machNumber_dimScale`, `froudeNumber_dimScale`,
  `biotNumber_dimScale` : unit invariance.
- `reynoldsNumber_si_mm`, `froudeNumber_si_mm` : nonzero fixtures in two coherent unit scales.
- `gasConstantDim_ne_specificHeatCapacityDim`,
  `dynamicViscosityDim_mul_gasConstantDim_div_thermalConductivityDim`,
  `gasConstantDim_div_molarMassDim`, `molarPrandtl_not_unitInvariant` : a molar heat capacity
  is not mass-specific, and inserting it unconverted gives a monomial of molar-mass dimension
  that changes with the unit scale.

## iii. Table of contents

- A. Engineering dimension names and exponents
- B. The dimensionless groups
- C. Dimension identities
- D. Coordinate formulas
- E. Unit invariance
- F. Fixtures in two unit scales
- G. A molar heat capacity in the Prandtl number

## iv. References

- ISO/IEC 80000-1, *Quantities and units — Part 1: General*: the seven ISQ base quantities.
- ISO 80000-11, *Quantities and units — Part 11: Characteristic numbers*: the Reynolds,
  Prandtl, Nusselt, Rayleigh, Mach, Froude and Biot numbers.
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and
  Mass Transfer*, Wiley: the Nusselt and Biot numbers with fluid and solid conductivities.
- `Physlib.Units.ParametricUnits` (`UnitScale.dimScale`),
  `PhyslibExt.Units.QuantityDimensions` (`dimScale_mul`, `dimScale_pos`) and
  `PhyslibExt.Units.EngineeringQuantities` (`powerDim`, `siScale`, `mmScale`).
-/

@[expose] public section

open Dimension Units.QuantityDimensions Units.EngineeringQuantities

namespace EngineeringScaling

/-! ## A. Engineering dimension names and exponents -/

/-- The velocity dimension `L T⁻¹`. -/
def velocityDim : Dimension ISQDimensionBase := single .length / single .time

/-- The acceleration dimension `L T⁻²`. -/
def accelerationDim : Dimension ISQDimensionBase := single .length / single .time ^ 2

/-- The mass density dimension `M L⁻³`. -/
def massDensityDim : Dimension ISQDimensionBase := single .mass / single .length ^ 3

/-- The dynamic viscosity dimension `M L⁻¹ T⁻¹`, a stress times a time. -/
def dynamicViscosityDim : Dimension ISQDimensionBase := stressDim * single .time

/-- The mass-specific heat capacity dimension `L² T⁻² Θ⁻¹`, an energy per mass and per
temperature. -/
def specificHeatCapacityDim : Dimension ISQDimensionBase :=
  energyDim / (single .mass * temperatureDim)

/-- The thermal conductivity dimension `M L T⁻³ Θ⁻¹`, a power per length and per
temperature. -/
def thermalConductivityDim : Dimension ISQDimensionBase :=
  powerDim / (single .length * temperatureDim)

/-- The heat transfer coefficient dimension `M T⁻³ Θ⁻¹`, a power per area and per
temperature. -/
def heatTransferCoefficientDim : Dimension ISQDimensionBase :=
  powerDim / (single .length ^ 2 * temperatureDim)

/-- The exponents of `velocityDim` at the seven ISQ base quantities. -/
lemma velocityDim_exponent (b : ISQDimensionBase) :
    velocityDim.exponent b =
      match b with
      | .length => 1
      | .mass => 0
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `accelerationDim` at the seven ISQ base quantities. -/
lemma accelerationDim_exponent (b : ISQDimensionBase) :
    accelerationDim.exponent b =
      match b with
      | .length => 1
      | .mass => 0
      | .time => -2
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `massDensityDim` at the seven ISQ base quantities. -/
lemma massDensityDim_exponent (b : ISQDimensionBase) :
    massDensityDim.exponent b =
      match b with
      | .length => -3
      | .mass => 1
      | .time => 0
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `dynamicViscosityDim` at the seven ISQ base quantities. -/
lemma dynamicViscosityDim_exponent (b : ISQDimensionBase) :
    dynamicViscosityDim.exponent b =
      match b with
      | .length => -1
      | .mass => 1
      | .time => -1
      | .current => 0
      | .temperature => 0
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `specificHeatCapacityDim` at the seven ISQ base quantities. -/
lemma specificHeatCapacityDim_exponent (b : ISQDimensionBase) :
    specificHeatCapacityDim.exponent b =
      match b with
      | .length => 2
      | .mass => 0
      | .time => -2
      | .current => 0
      | .temperature => -1
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `thermalConductivityDim` at the seven ISQ base quantities. -/
lemma thermalConductivityDim_exponent (b : ISQDimensionBase) :
    thermalConductivityDim.exponent b =
      match b with
      | .length => 1
      | .mass => 1
      | .time => -3
      | .current => 0
      | .temperature => -1
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-- The exponents of `heatTransferCoefficientDim` at the seven ISQ base quantities. -/
lemma heatTransferCoefficientDim_exponent (b : ISQDimensionBase) :
    heatTransferCoefficientDim.exponent b =
      match b with
      | .length => 0
      | .mass => 1
      | .time => -3
      | .current => 0
      | .temperature => -1
      | .amount => 0
      | .luminousIntensity => 0 := by
  cases b <;> decide

/-! ## B. The dimensionless groups -/

/-- The Reynolds number `Re = ρ |U| L / μ` of a mass density `ρ`, the speed `|U|` of a velocity
`U`, a length `L` and a dynamic viscosity `μ > 0`. -/
noncomputable def reynoldsNumber (ρ : WithDim massDensityDim ℝ) (U : WithDim velocityDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (μ : WithDim dynamicViscosityDim ℝ)
    (_hμ : 0 < μ.val) : ℝ :=
  (WithDim.cast (ρ * (⟨|U.val|⟩ : WithDim velocityDim ℝ) * L / μ)
    (by unfold dimensionlessDim; decide) : WithDim dimensionlessDim ℝ).val

/-- The Prandtl number `Pr = μ c_p / k` of a dynamic viscosity `μ`, a mass-specific heat
capacity `c_p` and a thermal conductivity `k > 0`. -/
noncomputable def prandtlNumber (μ : WithDim dynamicViscosityDim ℝ)
    (cp : WithDim specificHeatCapacityDim ℝ) (k : WithDim thermalConductivityDim ℝ)
    (_hk : 0 < k.val) : ℝ :=
  (WithDim.cast (μ * cp / k) (by unfold dimensionlessDim; decide) :
    WithDim dimensionlessDim ℝ).val

/-- The Nusselt number `Nu = h L / k` of a heat transfer coefficient `h`, a length `L` and the
thermal conductivity `k > 0` of the fluid. -/
noncomputable def nusseltNumber (h : WithDim heatTransferCoefficientDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (k : WithDim thermalConductivityDim ℝ)
    (_hk : 0 < k.val) : ℝ :=
  (WithDim.cast (h * L / k) (by unfold dimensionlessDim; decide) :
    WithDim dimensionlessDim ℝ).val

/-- The Rayleigh number `Ra = |g| β ΔT L ^ 3 / (ν κ)` of the magnitude `|g|` of a gravitational
acceleration `g`, a thermal expansion coefficient `β`, a temperature difference `ΔT`, a length
`L`, a kinematic viscosity `ν > 0` and a thermal diffusivity `κ > 0`. -/
noncomputable def rayleighNumber (g : WithDim accelerationDim ℝ)
    (β : WithDim temperatureDim⁻¹ ℝ) (ΔT : WithDim temperatureDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (ν κ : WithDim diffusivityDim ℝ)
    (_hν : 0 < ν.val) (_hκ : 0 < κ.val) : ℝ :=
  (WithDim.cast ((⟨|g.val|⟩ : WithDim accelerationDim ℝ) * β * ΔT * (L * L * L) / (ν * κ))
    (by unfold dimensionlessDim; decide) : WithDim dimensionlessDim ℝ).val

/-- The Mach number `Ma = |U| / a` of the speed `|U|` of a velocity `U` and a speed of sound
`a > 0`. -/
noncomputable def machNumber (U a : WithDim velocityDim ℝ) (_ha : 0 < a.val) : ℝ :=
  (WithDim.cast ((⟨|U.val|⟩ : WithDim velocityDim ℝ) / a)
    (by unfold dimensionlessDim; decide) : WithDim dimensionlessDim ℝ).val

/-- The Froude number `Fr = |U| / √(g L)` of the speed `|U|` of a velocity `U`, a gravitational
acceleration `g` and a length `L` with `g L > 0`. The square root is taken on coordinates; its
dimension identity is `froudeNumber_dimensionless`. -/
noncomputable def froudeNumber (U : WithDim velocityDim ℝ) (g : WithDim accelerationDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (_hgL : 0 < g.val * L.val) : ℝ :=
  |U.val| / Real.sqrt (g.val * L.val)

/-- The Biot number `Bi = h L / k_s` of a heat transfer coefficient `h`, a conduction length `L`
and the thermal conductivity `k_s > 0` of the solid. -/
noncomputable def biotNumber (h : WithDim heatTransferCoefficientDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (ks : WithDim thermalConductivityDim ℝ)
    (_hks : 0 < ks.val) : ℝ :=
  (WithDim.cast (h * L / ks) (by unfold dimensionlessDim; decide) :
    WithDim dimensionlessDim ℝ).val

/-! ## C. Dimension identities -/

/-- The Reynolds monomial `ρ U L / μ` is dimensionless. -/
lemma reynoldsNumber_dimensionless :
    massDensityDim * velocityDim * single .length / dynamicViscosityDim = 1 := by
  decide

/-- The Prandtl monomial `μ c_p / k` is dimensionless when `c_p` is mass-specific. -/
lemma prandtlNumber_dimensionless :
    dynamicViscosityDim * specificHeatCapacityDim / thermalConductivityDim = 1 := by
  decide

/-- The monomial `h L / k` of the Nusselt number, and of the Biot number with the solid
conductivity in place of `k`, is dimensionless. -/
lemma nusseltNumber_dimensionless :
    heatTransferCoefficientDim * single .length / thermalConductivityDim = 1 := by
  decide

/-- The Rayleigh monomial `g β ΔT L ^ 3 / (ν κ)` is dimensionless. -/
lemma rayleighNumber_dimensionless :
    accelerationDim * temperatureDim⁻¹ * temperatureDim * single .length ^ 3 /
      (diffusivityDim * diffusivityDim) = 1 := by
  decide

/-- The Froude monomial `U / (g L) ^ (1 / 2)` is dimensionless. -/
lemma froudeNumber_dimensionless :
    velocityDim / (accelerationDim * single .length) ^ (1 / 2 : Exponent) = 1 := by
  decide

/-! ## D. Coordinate formulas -/

/-- `reynoldsNumber ρ U L μ` is `ρ |U| L / μ` on coordinates. -/
lemma reynoldsNumber_val (ρ : WithDim massDensityDim ℝ) (U : WithDim velocityDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (μ : WithDim dynamicViscosityDim ℝ)
    (hμ : 0 < μ.val) :
    reynoldsNumber ρ U L μ hμ = ρ.val * |U.val| * L.val / μ.val := by
  rfl

/-- `prandtlNumber μ c_p k` is `μ c_p / k` on coordinates. -/
lemma prandtlNumber_val (μ : WithDim dynamicViscosityDim ℝ)
    (cp : WithDim specificHeatCapacityDim ℝ) (k : WithDim thermalConductivityDim ℝ)
    (hk : 0 < k.val) :
    prandtlNumber μ cp k hk = μ.val * cp.val / k.val := by
  rfl

/-- `nusseltNumber h L k` is `h L / k` on coordinates. -/
lemma nusseltNumber_val (h : WithDim heatTransferCoefficientDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (k : WithDim thermalConductivityDim ℝ)
    (hk : 0 < k.val) :
    nusseltNumber h L k hk = h.val * L.val / k.val := by
  rfl

/-- `rayleighNumber g β ΔT L ν κ` is `|g| β ΔT L ^ 3 / (ν κ)` on coordinates. -/
lemma rayleighNumber_val (g : WithDim accelerationDim ℝ) (β : WithDim temperatureDim⁻¹ ℝ)
    (ΔT : WithDim temperatureDim ℝ) (L : WithDim (single ISQDimensionBase.length) ℝ)
    (ν κ : WithDim diffusivityDim ℝ) (hν : 0 < ν.val) (hκ : 0 < κ.val) :
    rayleighNumber g β ΔT L ν κ hν hκ =
      |g.val| * β.val * ΔT.val * L.val ^ 3 / (ν.val * κ.val) := by
  change |g.val| * β.val * ΔT.val * (L.val * L.val * L.val) / (ν.val * κ.val) = _
  ring

/-- `machNumber U a` is `|U| / a` on coordinates. -/
lemma machNumber_val (U a : WithDim velocityDim ℝ) (ha : 0 < a.val) :
    machNumber U a ha = |U.val| / a.val := by
  rfl

/-- `biotNumber h L k_s` is `h L / k_s` on coordinates. -/
lemma biotNumber_val (h : WithDim heatTransferCoefficientDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) (ks : WithDim thermalConductivityDim ℝ)
    (hks : 0 < ks.val) :
    biotNumber h L ks hks = h.val * L.val / ks.val := by
  rfl

/-! ## E. Unit invariance -/

/-- The Reynolds number is unchanged by a change of units: each input rescales by the factor
for its own dimension. -/
lemma reynoldsNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (ρ : WithDim massDensityDim ℝ) (U : WithDim velocityDim ℝ)
    (L : WithDim (single ISQDimensionBase.length) ℝ) {μ : WithDim dynamicViscosityDim ℝ}
    (hμ : 0 < μ.val) :
    reynoldsNumber ⟨(u1.dimScale u2 massDensityDim : ℝ) * ρ.val⟩
        ⟨(u1.dimScale u2 velocityDim : ℝ) * U.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val⟩
        ⟨(u1.dimScale u2 dynamicViscosityDim : ℝ) * μ.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 dynamicViscosityDim)) hμ) =
      reynoldsNumber ρ U L μ hμ := by
  have hd : massDensityDim * velocityDim * single ISQDimensionBase.length =
      dynamicViscosityDim := by decide
  have hs : (u1.dimScale u2 massDensityDim : ℝ) * (u1.dimScale u2 velocityDim : ℝ) *
      (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) =
      (u1.dimScale u2 dynamicViscosityDim : ℝ) := by
    rw [← dimScale_mul, ← dimScale_mul, hd]
  have hne : (u1.dimScale u2 dynamicViscosityDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 dynamicViscosityDim)).ne'
  have hU : |(u1.dimScale u2 velocityDim : ℝ) * U.val| =
      (u1.dimScale u2 velocityDim : ℝ) * |U.val| := by
    rw [abs_mul, abs_of_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 velocityDim))]
  rw [reynoldsNumber_val, reynoldsNumber_val, hU]
  rw [show (u1.dimScale u2 massDensityDim : ℝ) * ρ.val *
      ((u1.dimScale u2 velocityDim : ℝ) * |U.val|) *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val) =
      (u1.dimScale u2 dynamicViscosityDim : ℝ) * (ρ.val * |U.val| * L.val) by rw [← hs]; ring]
  exact mul_div_mul_left _ _ hne

/-- The Prandtl number is unchanged by a change of units. -/
lemma prandtlNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (μ : WithDim dynamicViscosityDim ℝ) (cp : WithDim specificHeatCapacityDim ℝ)
    {k : WithDim thermalConductivityDim ℝ} (hk : 0 < k.val) :
    prandtlNumber ⟨(u1.dimScale u2 dynamicViscosityDim : ℝ) * μ.val⟩
        ⟨(u1.dimScale u2 specificHeatCapacityDim : ℝ) * cp.val⟩
        ⟨(u1.dimScale u2 thermalConductivityDim : ℝ) * k.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)) hk) =
      prandtlNumber μ cp k hk := by
  have hd : dynamicViscosityDim * specificHeatCapacityDim = thermalConductivityDim := by decide
  have hs : (u1.dimScale u2 dynamicViscosityDim : ℝ) *
      (u1.dimScale u2 specificHeatCapacityDim : ℝ) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) := by
    rw [← dimScale_mul, hd]
  have hne : (u1.dimScale u2 thermalConductivityDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)).ne'
  rw [prandtlNumber_val, prandtlNumber_val]
  rw [show (u1.dimScale u2 dynamicViscosityDim : ℝ) * μ.val *
      ((u1.dimScale u2 specificHeatCapacityDim : ℝ) * cp.val) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) * (μ.val * cp.val) by rw [← hs]; ring]
  exact mul_div_mul_left _ _ hne

/-- The Nusselt number is unchanged by a change of units. -/
lemma nusseltNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (h : WithDim heatTransferCoefficientDim ℝ) (L : WithDim (single ISQDimensionBase.length) ℝ)
    {k : WithDim thermalConductivityDim ℝ} (hk : 0 < k.val) :
    nusseltNumber ⟨(u1.dimScale u2 heatTransferCoefficientDim : ℝ) * h.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val⟩
        ⟨(u1.dimScale u2 thermalConductivityDim : ℝ) * k.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)) hk) =
      nusseltNumber h L k hk := by
  have hd : heatTransferCoefficientDim * single ISQDimensionBase.length =
      thermalConductivityDim := by decide
  have hs : (u1.dimScale u2 heatTransferCoefficientDim : ℝ) *
      (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) := by
    rw [← dimScale_mul, hd]
  have hne : (u1.dimScale u2 thermalConductivityDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)).ne'
  rw [nusseltNumber_val, nusseltNumber_val]
  rw [show (u1.dimScale u2 heatTransferCoefficientDim : ℝ) * h.val *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) * (h.val * L.val) by rw [← hs]; ring]
  exact mul_div_mul_left _ _ hne

/-- The Rayleigh number is unchanged by a change of units. -/
lemma rayleighNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (g : WithDim accelerationDim ℝ) (β : WithDim temperatureDim⁻¹ ℝ)
    (ΔT : WithDim temperatureDim ℝ) (L : WithDim (single ISQDimensionBase.length) ℝ)
    {ν κ : WithDim diffusivityDim ℝ} (hν : 0 < ν.val) (hκ : 0 < κ.val) :
    rayleighNumber ⟨(u1.dimScale u2 accelerationDim : ℝ) * g.val⟩
        ⟨(u1.dimScale u2 temperatureDim⁻¹ : ℝ) * β.val⟩
        ⟨(u1.dimScale u2 temperatureDim : ℝ) * ΔT.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val⟩
        ⟨(u1.dimScale u2 diffusivityDim : ℝ) * ν.val⟩
        ⟨(u1.dimScale u2 diffusivityDim : ℝ) * κ.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 diffusivityDim)) hν)
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 diffusivityDim)) hκ) =
      rayleighNumber g β ΔT L ν κ hν hκ := by
  have hd : accelerationDim * temperatureDim⁻¹ * temperatureDim *
      (single ISQDimensionBase.length * single ISQDimensionBase.length *
        single ISQDimensionBase.length) = diffusivityDim * diffusivityDim := by decide
  have hs : (u1.dimScale u2 accelerationDim : ℝ) * (u1.dimScale u2 temperatureDim⁻¹ : ℝ) *
      (u1.dimScale u2 temperatureDim : ℝ) *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) *
        (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) *
        (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ)) =
      (u1.dimScale u2 diffusivityDim : ℝ) * (u1.dimScale u2 diffusivityDim : ℝ) := by
    rw [← dimScale_mul, ← dimScale_mul, ← dimScale_mul, ← dimScale_mul, ← dimScale_mul,
      ← dimScale_mul, hd]
  have hne : (u1.dimScale u2 diffusivityDim : ℝ) * (u1.dimScale u2 diffusivityDim : ℝ) ≠ 0 :=
    (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 diffusivityDim))
      (NNReal.coe_pos.mpr (dimScale_pos u1 u2 diffusivityDim))).ne'
  have hg : |(u1.dimScale u2 accelerationDim : ℝ) * g.val| =
      (u1.dimScale u2 accelerationDim : ℝ) * |g.val| := by
    rw [abs_mul, abs_of_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 accelerationDim))]
  rw [rayleighNumber_val, rayleighNumber_val, hg]
  rw [show (u1.dimScale u2 accelerationDim : ℝ) * |g.val| *
      ((u1.dimScale u2 temperatureDim⁻¹ : ℝ) * β.val) *
      ((u1.dimScale u2 temperatureDim : ℝ) * ΔT.val) *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val) ^ 3 =
      ((u1.dimScale u2 diffusivityDim : ℝ) * (u1.dimScale u2 diffusivityDim : ℝ)) *
        (|g.val| * β.val * ΔT.val * L.val ^ 3) by rw [← hs]; ring]
  rw [show (u1.dimScale u2 diffusivityDim : ℝ) * ν.val *
      ((u1.dimScale u2 diffusivityDim : ℝ) * κ.val) =
      ((u1.dimScale u2 diffusivityDim : ℝ) * (u1.dimScale u2 diffusivityDim : ℝ)) *
        (ν.val * κ.val) by ring]
  exact mul_div_mul_left _ _ hne

/-- The Mach number is unchanged by a change of units. -/
lemma machNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase) (U : WithDim velocityDim ℝ)
    {a : WithDim velocityDim ℝ} (ha : 0 < a.val) :
    machNumber ⟨(u1.dimScale u2 velocityDim : ℝ) * U.val⟩
        ⟨(u1.dimScale u2 velocityDim : ℝ) * a.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 velocityDim)) ha) =
      machNumber U a ha := by
  have hne : (u1.dimScale u2 velocityDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 velocityDim)).ne'
  have hU : |(u1.dimScale u2 velocityDim : ℝ) * U.val| =
      (u1.dimScale u2 velocityDim : ℝ) * |U.val| := by
    rw [abs_mul, abs_of_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 velocityDim))]
  rw [machNumber_val, machNumber_val, hU]
  exact mul_div_mul_left _ _ hne

/-- The Froude number is unchanged by a change of units: `g L` rescales by the square of the
velocity factor, whose square root is that factor. -/
lemma froudeNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase) (U : WithDim velocityDim ℝ)
    {g : WithDim accelerationDim ℝ} {L : WithDim (single ISQDimensionBase.length) ℝ}
    (hgL : 0 < g.val * L.val) :
    froudeNumber ⟨(u1.dimScale u2 velocityDim : ℝ) * U.val⟩
        ⟨(u1.dimScale u2 accelerationDim : ℝ) * g.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val⟩
        (by
          rw [mul_mul_mul_comm]
          exact mul_pos (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 _))
            (NNReal.coe_pos.mpr (dimScale_pos u1 u2 _))) hgL) =
      froudeNumber U g L hgL := by
  have hd : accelerationDim * single ISQDimensionBase.length = velocityDim * velocityDim := by
    decide
  have hs : (u1.dimScale u2 accelerationDim : ℝ) *
      (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) =
      (u1.dimScale u2 velocityDim : ℝ) ^ 2 := by
    rw [← dimScale_mul, hd, dimScale_mul, sq]
  have hpos : 0 < (u1.dimScale u2 velocityDim : ℝ) :=
    NNReal.coe_pos.mpr (dimScale_pos u1 u2 velocityDim)
  unfold froudeNumber
  dsimp only
  rw [abs_mul, abs_of_pos hpos]
  rw [show (u1.dimScale u2 accelerationDim : ℝ) * g.val *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val) =
      (u1.dimScale u2 velocityDim : ℝ) ^ 2 * (g.val * L.val) by rw [← hs]; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
  exact mul_div_mul_left _ _ hpos.ne'

/-- The Biot number is unchanged by a change of units. -/
lemma biotNumber_dimScale (u1 u2 : UnitScale ISQDimensionBase)
    (h : WithDim heatTransferCoefficientDim ℝ) (L : WithDim (single ISQDimensionBase.length) ℝ)
    {ks : WithDim thermalConductivityDim ℝ} (hks : 0 < ks.val) :
    biotNumber ⟨(u1.dimScale u2 heatTransferCoefficientDim : ℝ) * h.val⟩
        ⟨(u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val⟩
        ⟨(u1.dimScale u2 thermalConductivityDim : ℝ) * ks.val⟩
        (mul_pos (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)) hks) =
      biotNumber h L ks hks := by
  have hd : heatTransferCoefficientDim * single ISQDimensionBase.length =
      thermalConductivityDim := by decide
  have hs : (u1.dimScale u2 heatTransferCoefficientDim : ℝ) *
      (u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) := by
    rw [← dimScale_mul, hd]
  have hne : (u1.dimScale u2 thermalConductivityDim : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (dimScale_pos u1 u2 thermalConductivityDim)).ne'
  rw [biotNumber_val, biotNumber_val]
  rw [show (u1.dimScale u2 heatTransferCoefficientDim : ℝ) * h.val *
      ((u1.dimScale u2 (single ISQDimensionBase.length) : ℝ) * L.val) =
      (u1.dimScale u2 thermalConductivityDim : ℝ) * (h.val * L.val) by rw [← hs]; ring]
  exact mul_div_mul_left _ _ hne

-- `ΔT` in the Rayleigh number is a temperature difference: Celsius and kelvin differences
-- agree (reused from `PhyslibExt.Units.QuantityDimensions`), while a Celsius reading is
-- affine and is not a `UnitScale` coordinate.
example (t1 t2 : ℝ) : celsiusToKelvin t2 - celsiusToKelvin t1 = t2 - t1 :=
  celsiusToKelvin_sub_celsiusToKelvin t1 t2

/-! ## F. Fixtures in two unit scales -/

/-- From metres to millimetres, a length coordinate is multiplied by `1000`. -/
private lemma dimScale_si_mm_length :
    (siScale.dimScale mmScale (single ISQDimensionBase.length) : ℝ) = 1000 := by
  rw [dimScale_single]
  simp [siScale, mmScale]

/-- From metres to millimetres, every base quantity other than length keeps the factor `1`. -/
private lemma dimScale_si_mm_single_of_ne {b : ISQDimensionBase} (hb : b ≠ .length) :
    (siScale.dimScale mmScale (single b) : ℝ) = 1 := by
  rw [dimScale_single]
  simp [siScale, mmScale, hb]

/-- From metres to millimetres, a mass density coordinate is multiplied by `1 / 1000000000`. -/
private lemma dimScale_si_mm_massDensityDim :
    (siScale.dimScale mmScale massDensityDim : ℝ) = 1 / 1000000000 := by
  rw [show massDensityDim = single .mass * (single .length * single .length * single .length)⁻¹
    by decide, dimScale_mul, dimScale_inv, dimScale_mul, dimScale_mul, dimScale_si_mm_length,
    dimScale_si_mm_single_of_ne (by decide)]
  norm_num

/-- From metres to millimetres, a velocity coordinate is multiplied by `1000`. -/
private lemma dimScale_si_mm_velocityDim :
    (siScale.dimScale mmScale velocityDim : ℝ) = 1000 := by
  rw [show velocityDim = single .length * (single .time)⁻¹ by decide, dimScale_mul,
    dimScale_inv, dimScale_si_mm_length, dimScale_si_mm_single_of_ne (by decide)]
  norm_num

/-- From metres to millimetres, an acceleration coordinate is multiplied by `1000`. -/
private lemma dimScale_si_mm_accelerationDim :
    (siScale.dimScale mmScale accelerationDim : ℝ) = 1000 := by
  rw [show accelerationDim = single .length * (single .time * single .time)⁻¹ by decide,
    dimScale_mul, dimScale_inv, dimScale_mul, dimScale_si_mm_length,
    dimScale_si_mm_single_of_ne (by decide)]
  norm_num

/-- From metres to millimetres, a dynamic viscosity coordinate is multiplied by `1 / 1000`. -/
private lemma dimScale_si_mm_dynamicViscosityDim :
    (siScale.dimScale mmScale dynamicViscosityDim : ℝ) = 1 / 1000 := by
  rw [show dynamicViscosityDim = single .mass * (single .length * single .time)⁻¹ by decide,
    dimScale_mul, dimScale_inv, dimScale_mul, dimScale_si_mm_length,
    dimScale_si_mm_single_of_ne (by decide), dimScale_si_mm_single_of_ne (by decide)]
  norm_num

/-- Water-like flow with `ρ = 1000`, `U = 2`, `L = 1 / 10` and `μ = 1 / 1000` in base SI
units has `Re = 200000`. In the millimetre scale the four coordinates become `1 / 1000000`,
`2000`, `100` and `1 / 1000000`, and `Re` is again `200000`. -/
lemma reynoldsNumber_si_mm :
    (siScale.dimScale mmScale massDensityDim : ℝ) * 1000 = 1 / 1000000 ∧
      (siScale.dimScale mmScale velocityDim : ℝ) * 2 = 2000 ∧
      (siScale.dimScale mmScale (single ISQDimensionBase.length) : ℝ) * (1 / 10) = 100 ∧
      (siScale.dimScale mmScale dynamicViscosityDim : ℝ) * (1 / 1000) = 1 / 1000000 ∧
      reynoldsNumber ⟨1000⟩ ⟨2⟩ ⟨1 / 10⟩ ⟨1 / 1000⟩ (by norm_num) = 200000 ∧
      reynoldsNumber ⟨1 / 1000000⟩ ⟨2000⟩ ⟨100⟩ ⟨1 / 1000000⟩ (by norm_num) = 200000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dimScale_si_mm_massDensityDim]; norm_num
  · rw [dimScale_si_mm_velocityDim]; norm_num
  · rw [dimScale_si_mm_length]; norm_num
  · rw [dimScale_si_mm_dynamicViscosityDim]; norm_num
  · rw [reynoldsNumber_val]; norm_num
  · rw [reynoldsNumber_val]; norm_num

/-- With `U = 3`, `g = 10` and `L = 5 / 2` in base SI units, `g L = 25` and `Fr = 3 / 5`.
In the millimetre scale the coordinates become `3000`, `10000` and `2500`, `g L = 25000000`,
and `Fr` is again `3 / 5`. -/
lemma froudeNumber_si_mm :
    (siScale.dimScale mmScale velocityDim : ℝ) * 3 = 3000 ∧
      (siScale.dimScale mmScale accelerationDim : ℝ) * 10 = 10000 ∧
      (siScale.dimScale mmScale (single ISQDimensionBase.length) : ℝ) * (5 / 2) = 2500 ∧
      froudeNumber ⟨3⟩ ⟨10⟩ ⟨5 / 2⟩ (by norm_num) = 3 / 5 ∧
      froudeNumber ⟨3000⟩ ⟨10000⟩ ⟨2500⟩ (by norm_num) = 3 / 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [dimScale_si_mm_velocityDim]; norm_num
  · rw [dimScale_si_mm_accelerationDim]; norm_num
  · rw [dimScale_si_mm_length]; norm_num
  · unfold froudeNumber
    dsimp only
    rw [show (10 : ℝ) * (5 / 2) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  · unfold froudeNumber
    dsimp only
    rw [show (10000 : ℝ) * 2500 = 5000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-! ## G. A molar heat capacity in the Prandtl number -/

/-- A molar heat capacity, of the dimension `gasConstantDim` of the molar gas constant, is not
a mass-specific heat capacity, so it is not an admissible argument of `prandtlNumber`. -/
lemma gasConstantDim_ne_specificHeatCapacityDim :
    gasConstantDim ≠ specificHeatCapacityDim := by
  decide

/-- With a molar heat capacity in place of `c_p`, the Prandtl monomial `μ c / k` has the
molar-mass dimension `M N⁻¹`, not `1`. -/
lemma dynamicViscosityDim_mul_gasConstantDim_div_thermalConductivityDim :
    dynamicViscosityDim * gasConstantDim / thermalConductivityDim = molarMassDim := by
  decide

/-- Dividing a molar heat capacity by a molar mass gives a mass-specific heat capacity: the
conversion that must precede the Prandtl number. -/
lemma gasConstantDim_div_molarMassDim :
    gasConstantDim / molarMassDim = specificHeatCapacityDim := by
  decide

/-- The scale `siScale` with the amount unit replaced by the kilomole, of magnitude `1000`
mole. -/
private noncomputable def kmolScale : UnitScale ISQDimensionBase where
  scale b := if b = .amount then 1000 else 1
  scale_pos b := by
    split_ifs
    · norm_num
    · exact one_pos

/-- From moles to kilomoles, an amount coordinate is multiplied by `1 / 1000`. -/
private lemma dimScale_si_kmol_amount :
    (siScale.dimScale kmolScale (single ISQDimensionBase.amount) : ℝ) = 1 / 1000 := by
  rw [dimScale_single]
  simp [siScale, kmolScale]

/-- From moles to kilomoles, every base quantity other than amount keeps the factor `1`. -/
private lemma dimScale_si_kmol_single_of_ne {b : ISQDimensionBase} (hb : b ≠ .amount) :
    (siScale.dimScale kmolScale (single b) : ℝ) = 1 := by
  rw [dimScale_single]
  simp [siScale, kmolScale, hb]

/-- From moles to kilomoles, a dynamic viscosity coordinate is unchanged. -/
private lemma dimScale_si_kmol_dynamicViscosityDim :
    (siScale.dimScale kmolScale dynamicViscosityDim : ℝ) = 1 := by
  rw [show dynamicViscosityDim = single .mass * (single .length * single .time)⁻¹ by decide,
    dimScale_mul, dimScale_inv, dimScale_mul, dimScale_si_kmol_single_of_ne (by decide),
    dimScale_si_kmol_single_of_ne (by decide), dimScale_si_kmol_single_of_ne (by decide)]
  norm_num

/-- From moles to kilomoles, a molar heat capacity coordinate is multiplied by `1000`. -/
private lemma dimScale_si_kmol_gasConstantDim :
    (siScale.dimScale kmolScale gasConstantDim : ℝ) = 1000 := by
  rw [show gasConstantDim = single .mass * (single .length * single .length) *
      (single .time * single .time * single .amount * single .temperature)⁻¹ by decide,
    dimScale_mul, dimScale_mul, dimScale_inv, dimScale_mul, dimScale_mul, dimScale_mul,
    dimScale_mul, dimScale_si_kmol_amount,
    dimScale_si_kmol_single_of_ne (b := .mass) (by decide),
    dimScale_si_kmol_single_of_ne (b := .length) (by decide),
    dimScale_si_kmol_single_of_ne (b := .time) (by decide),
    dimScale_si_kmol_single_of_ne (b := .temperature) (by decide)]
  norm_num

/-- From moles to kilomoles, a thermal conductivity coordinate is unchanged. -/
private lemma dimScale_si_kmol_thermalConductivityDim :
    (siScale.dimScale kmolScale thermalConductivityDim : ℝ) = 1 := by
  rw [show thermalConductivityDim = single .mass * single .length *
      (single .time * single .time * single .time * single .temperature)⁻¹ by decide,
    dimScale_mul, dimScale_mul, dimScale_inv, dimScale_mul, dimScale_mul, dimScale_mul,
    dimScale_si_kmol_single_of_ne (b := .mass) (by decide),
    dimScale_si_kmol_single_of_ne (b := .length) (by decide),
    dimScale_si_kmol_single_of_ne (b := .time) (by decide),
    dimScale_si_kmol_single_of_ne (b := .temperature) (by decide)]
  norm_num

/-- Inserting an unconverted molar heat capacity `c` into the Prandtl formula gives a value
`μ c / k` that depends on the unit scale: for some unit scales and positive coordinates, the
rescaled value differs from the original. -/
lemma molarPrandtl_not_unitInvariant :
    ∃ (u1 u2 : UnitScale ISQDimensionBase) (μ c k : ℝ), 0 < μ ∧ 0 < c ∧ 0 < k ∧
      (u1.dimScale u2 dynamicViscosityDim : ℝ) * μ *
          ((u1.dimScale u2 gasConstantDim : ℝ) * c) /
          ((u1.dimScale u2 thermalConductivityDim : ℝ) * k) ≠ μ * c / k := by
  refine ⟨siScale, kmolScale, 1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
  rw [dimScale_si_kmol_dynamicViscosityDim, dimScale_si_kmol_gasConstantDim,
    dimScale_si_kmol_thermalConductivityDim]
  norm_num

end EngineeringScaling
