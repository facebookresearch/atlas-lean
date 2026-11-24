/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.HeatTransfer.CorrelationDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Range-guarded correlation checks

Concrete consumer of `PhyslibExt.HeatTransfer.CorrelationDomains`: the
Dittus-Boelter correlation, one record per thermal direction, for
hydrodynamically and thermally fully developed flow in a smooth
circular tube at small to moderate temperature differences, with its published domain `Re ≥ 10000`,
`0.7 ≤ Pr ≤ 160`, `L / D ≥ 10`, the local tag, properties at the mean
temperature and the exponent `2/5` for heating or `3/10` for cooling.
A heated tube flow with `Re = 100000`, `Pr = 1`, `L / D = 20` and
`ΔT = 10` is a valid request and gives
`Nu = 230`, `h = 2760` for `k = 3 / 5` and `D = 1 / 20`, and on
`A = 1 / 10` the heat rate `2760`; the same flow cooled with `ΔT = -10`
uses the cooling record and gives `-2760`. At `Pr = 32` the exponent
selected by the thermal direction changes the value. A cooled flow
for the heating record, a flat plate in parallel flow, a
hydrodynamically or a thermally developing flow and a
large-property-variation flow with otherwise identical data, a short
duct, values outside the domain (including `Pr = 161`), `ΔT = 0`,
film-temperature properties and a surface-averaged request are
rejected; the bounds are inclusive, so `Pr = 160` and the corner
`Re = 10000`, `Pr = 0.7`, `L / D = 10` are accepted. A guard probe
recorded for a thermal entry length separates the two opposite
one-sided development regimes, and the Sieder-Tate correlation for
large property variation gives different values for two requests that
differ only in the viscosity ratio `μ_m / μ_s`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the
Dittus-Boelter and Sieder-Tate records, the guard probe and the heated
request it checks.

## iii. Table of contents

- A. The Dittus-Boelter correlation

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine,
  *Fundamentals of Heat and Mass Transfer*, Wiley, chapter 8 (the
  Dittus-Boelter correlation, its exponents and its range).
-/

@[expose] public section

namespace PhyslibExtTest.HeatTransfer.CorrelationDomains

open Dimension Units.QuantityDimensions Units.EngineeringQuantities EngineeringScaling
open _root_.CorrelationDomains

/-! ## A. The Dittus-Boelter correlation -/

/-- The Dittus-Boelter Prandtl exponent: `2/5` when the fluid is heated, `3/10` when it is
cooled. -/
noncomputable def dittusBoelterExponent : ThermalMode → ℝ
  | .heating => 2 / 5
  | .cooling => 3 / 10

/-- The Dittus-Boelter correlation for the thermal direction `m`:
`Nu = 0.023 Re ^ (4/5) Pr ^ n` with `n = dittusBoelterExponent m`, the local value for fully
developed turbulent flow (hydrodynamically and thermally) in a smooth circular tube at small to
moderate temperature differences, properties at the mean (bulk) temperature, and the published
domain `Re ≥ 10000`, `0.7 ≤ Pr ≤ 160`, `L / D ≥ 10`, with the request's temperature difference
in the direction `m`. -/
noncomputable def dittusBoelter (m : ThermalMode) : NusseltCorrelation :=
  powerLawCorrelation (23 / 1000) (4 / 5) (dittusBoelterExponent m)
    "Dittus-Boelter, in Incropera et al., Fundamentals of Heat and Mass Transfer"
    FlowConfiguration.smoothCircularTube FlowDevelopment.fullyDeveloped
    FlowDevelopment.fullyDeveloped PropertyVariation.smallToModerate AveragingTag.localValue
    PropertyTemperature.bulkMean
    {s | 10000 ≤ s.reynolds ∧ 7 / 10 ≤ s.prandtl ∧ s.prandtl ≤ 160 ∧ 10 ≤ s.lengthRatio ∧
      m.Holds s.temperatureDifference.val}
    (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2.1]⟩)
    (by
      cases m
      · exact ⟨⟨10000, 1, 10, ⟨1⟩, 1⟩, by norm_num [ThermalMode.Holds]⟩
      · exact ⟨⟨10000, 1, 10, ⟨-1⟩, 1⟩, by norm_num [ThermalMode.Holds]⟩)

/-- Where a Dittus-Boelter record applies, it evaluates to `0.023 Re ^ (4/5) Pr ^ n`. -/
lemma dittusBoelter_nusselt {m : ThermalMode} {r : CorrelationRequest}
    (h : (dittusBoelter m).Applies r) :
    (dittusBoelter m).nusselt r h =
      23 / 1000 * r.reynolds ^ (4 / 5 : ℝ) * r.prandtl ^ dittusBoelterExponent m :=
  powerLawCorrelation_nusselt h

/-- A heated, fully developed flow in a smooth circular tube: `Re = 100000`, `Pr = 1`,
`L / D = 20`, the surface `10` K above the mean fluid temperature (a small temperature
difference, so the viscosity ratio is `μ_m / μ_s = 1`), a local value requested, properties at the
mean temperature. -/
def heatingRequest : CorrelationRequest where
  reynolds := 100000
  prandtl := 1
  lengthRatio := 20
  temperatureDifference := ⟨10⟩
  viscosityRatio := 1
  configuration := FlowConfiguration.smoothCircularTube
  hydrodynamicDevelopment := FlowDevelopment.fullyDeveloped
  thermalDevelopment := FlowDevelopment.fullyDeveloped
  propertyVariation := PropertyVariation.smallToModerate
  averaging := AveragingTag.localValue
  propertyTemperature := PropertyTemperature.bulkMean

/-- The heated tube flow is a valid request for the heating correlation. -/
lemma dittusBoelter_applies_heating : (dittusBoelter .heating).Applies heatingRequest := by
  simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
    Set.mem_ofPred_eq, ThermalMode.Holds]
  norm_num

/-- A nonzero `ΔT` in the valid domain: with `ρ = 1000`, `U = 2`, `D = 1 / 20`, `μ = 1 / 1000`,
`c_p = 600` and `k = 3 / 5` (SI), `Re = 100000` and `Pr = 1`; through the guard the heating
correlation gives `Nu = 230`, so `h = 2760`, and on `A = 1 / 10` the heat rate at the request's
`ΔT = 10` is `2760`, into the fluid. -/
example :
    reynoldsNumber ⟨1000⟩ ⟨2⟩ ⟨1 / 20⟩ ⟨1 / 1000⟩ (by norm_num) = heatingRequest.reynolds ∧
      prandtlNumber ⟨1 / 1000⟩ ⟨600⟩ ⟨3 / 5⟩ (by norm_num) = heatingRequest.prandtl ∧
      (dittusBoelter .heating).nusselt heatingRequest dittusBoelter_applies_heating = 230 ∧
      (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)).val = 2760 ∧
      (convectiveHeatRate (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩
        heatingRequest.temperatureDifference).val = 2760 := by
  have h1 : (100000 : ℝ) ^ (4 / 5 : ℝ) = 10000 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [reynoldsNumber_val]; norm_num [heatingRequest]
  · rw [prandtlNumber_val]; norm_num [heatingRequest]
  · rw [dittusBoelter_nusselt dittusBoelter_applies_heating]
    simp only [heatingRequest, dittusBoelterExponent]
    rw [h1, Real.one_rpow]
    norm_num
  · simp only [heatTransferCoefficient]; norm_num
  · rw [convectiveHeatRate_val]; simp only [heatTransferCoefficient, heatingRequest]; norm_num

/-- The same tube cooling the fluid, `ΔT = -10`, is a valid request for the cooling correlation
with the exponent `3/10`; at `Pr = 1` it also gives `Nu = 230`, and the heat rate is `-2760`, out
of the fluid. -/
example :
    ∃ h : (dittusBoelter .cooling).Applies { heatingRequest with temperatureDifference := ⟨-10⟩ },
      (dittusBoelter .cooling).nusselt _ h = 230 ∧
      (convectiveHeatRate (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩
        ⟨-10⟩).val = -2760 := by
  have happ : (dittusBoelter .cooling).Applies
      { heatingRequest with temperatureDifference := ⟨-10⟩ } := by
    simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq, ThermalMode.Holds]
    norm_num
  have h1 : (100000 : ℝ) ^ (4 / 5 : ℝ) = 10000 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨happ, ?_, ?_⟩
  · rw [dittusBoelter_nusselt happ]
    simp only [heatingRequest, dittusBoelterExponent]
    rw [h1, Real.one_rpow]
    norm_num
  · rw [convectiveHeatRate_val]; simp only [heatTransferCoefficient]; norm_num

/-- The thermal direction selects the exponent: at `Re = 100000` and `Pr = 32` the heated flow has
`Nu = 0.023 · 10000 · 32 ^ (2/5) = 920`, and the cooled flow has the smaller
`Nu = 0.023 · 10000 · 32 ^ (3/10)`. -/
example :
    ∃ (hh : (dittusBoelter .heating).Applies { heatingRequest with prandtl := 32 })
      (hc : (dittusBoelter .cooling).Applies
        { heatingRequest with prandtl := 32, temperatureDifference := ⟨-10⟩ }),
      (dittusBoelter .heating).nusselt _ hh = 920 ∧
        (dittusBoelter .cooling).nusselt _ hc < (dittusBoelter .heating).nusselt _ hh := by
  have hh : (dittusBoelter .heating).Applies { heatingRequest with prandtl := 32 } := by
    simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq, ThermalMode.Holds]
    norm_num
  have hc : (dittusBoelter .cooling).Applies
      { heatingRequest with prandtl := 32, temperatureDifference := ⟨-10⟩ } := by
    simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq, ThermalMode.Holds]
    norm_num
  have h1 : (100000 : ℝ) ^ (4 / 5 : ℝ) = 10000 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h32 : (32 : ℝ) ^ (2 / 5 : ℝ) = 4 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlt : (32 : ℝ) ^ (3 / 10 : ℝ) < (32 : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  refine ⟨hh, hc, ?_, ?_⟩
  · rw [dittusBoelter_nusselt hh]
    simp only [heatingRequest, dittusBoelterExponent]
    rw [h1, h32]
    norm_num
  · rw [dittusBoelter_nusselt hh, dittusBoelter_nusselt hc]
    simp only [heatingRequest, dittusBoelterExponent]
    rw [h1]
    nlinarith

/-- Rejections: the heating correlation does not apply to the cooled flow (`ΔT = -10`), and no
Dittus-Boelter correlation applies, with otherwise identical data, to a flat plate in parallel
flow, to a developing flow, or to a flow with large property variation, nor to a short duct
(`L / D = 5`), to `Re = 5000`, to `Pr = 13 / 20` (below `0.7`),
`Pr = 1 / 2` or `Pr = 161` (above `160`), to a flow without a thermal direction (`ΔT = 0`), to
properties at the film temperature, or to a surface-averaged request. -/
example :
    ¬ (dittusBoelter .heating).Applies { heatingRequest with temperatureDifference := ⟨-10⟩ } ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with configuration := FlowConfiguration.flatPlateParallelFlow }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with hydrodynamicDevelopment := FlowDevelopment.developing }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with thermalDevelopment := FlowDevelopment.developing }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with propertyVariation := PropertyVariation.large }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with lengthRatio := 5 }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with reynolds := 5000 }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with prandtl := 13 / 20 }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with prandtl := 1 / 2 }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with prandtl := 161 }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies { heatingRequest with temperatureDifference := ⟨0⟩ }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with propertyTemperature := PropertyTemperature.film }) ∧
      (∀ m, ¬ (dittusBoelter m).Applies
        { heatingRequest with averaging := AveragingTag.surfaceAverage }) := by
  refine ⟨?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_,
    fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_, fun m => ?_⟩ <;>
    (try cases m) <;>
    simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq, ThermalMode.Holds] <;>
    norm_num

/-- A guard probe, not a published correlation: `Nu = 1` on positive `Re` and `Pr`, recorded as
calibrated for a smooth circular tube with a hydrodynamically fully developed, thermally developing
flow (a thermal entry length). It only tests that the two development fields are guarded
separately. -/
noncomputable def thermalEntryProbe : NusseltCorrelation :=
  powerLawCorrelation 1 0 0 "guard probe, not a published correlation"
    FlowConfiguration.smoothCircularTube FlowDevelopment.fullyDeveloped FlowDevelopment.developing
    PropertyVariation.smallToModerate AveragingTag.localValue PropertyTemperature.bulkMean
    {s | 0 < s.reynolds ∧ 0 < s.prandtl} (fun _ hs => hs) ⟨⟨1, 1, 1, ⟨1⟩, 1⟩, by norm_num⟩

/-- The hydrodynamic and the thermal development are guarded separately. The heating record
accepts the fully developed flow and rejects both one-sided entrance regions with otherwise
identical numbers; a record for hydrodynamically developed, thermally developing flow accepts that
regime and rejects the opposite one, hydrodynamically developing and thermally developed. -/
example :
    (dittusBoelter .heating).Applies heatingRequest ∧
      ¬ (dittusBoelter .heating).Applies
        { heatingRequest with hydrodynamicDevelopment := FlowDevelopment.developing } ∧
      ¬ (dittusBoelter .heating).Applies
        { heatingRequest with thermalDevelopment := FlowDevelopment.developing } ∧
      thermalEntryProbe.Applies
        { heatingRequest with thermalDevelopment := FlowDevelopment.developing } ∧
      ¬ thermalEntryProbe.Applies
        { heatingRequest with hydrodynamicDevelopment := FlowDevelopment.developing } := by
  refine ⟨dittusBoelter_applies_heating, fun h => ?_, fun h => ?_, ?_, fun h => ?_⟩
  · exact absurd h.2.1 (by simp [dittusBoelter, powerLawCorrelation])
  · exact absurd h.2.2.1 (by simp [dittusBoelter, powerLawCorrelation])
  · simp only [thermalEntryProbe, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq]
    norm_num
  · exact absurd h.2.1 (by simp [thermalEntryProbe, powerLawCorrelation])

/-- The Sieder-Tate correlation for large property variation,
`Nu = 0.027 Re ^ (4/5) Pr ^ (1/3) (μ_m / μ_s) ^ 0.14`: the local value for hydrodynamically and
thermally fully developed turbulent flow in a smooth circular tube, properties at the mean
temperature except the surface viscosity in `μ_m / μ_s`, and the published domain `Re ≥ 10000`,
`0.7 ≤ Pr ≤ 16700`, `L / D ≥ 10`. -/
noncomputable def siederTate : NusseltCorrelation where
  citation := "Sieder-Tate, in Incropera et al., Fundamentals of Heat and Mass Transfer"
  configuration := FlowConfiguration.smoothCircularTube
  hydrodynamicDevelopment := FlowDevelopment.fullyDeveloped
  thermalDevelopment := FlowDevelopment.fullyDeveloped
  propertyVariation := PropertyVariation.large
  averaging := AveragingTag.localValue
  propertyTemperature := PropertyTemperature.bulkMean
  validity := {s | 10000 ≤ s.reynolds ∧ 7 / 10 ≤ s.prandtl ∧ s.prandtl ≤ 16700 ∧
    10 ≤ s.lengthRatio ∧ 0 < s.viscosityRatio}
  validity_pos _ hs := ⟨by linarith [hs.1], by linarith [hs.2.1]⟩
  validity_nonempty := ⟨⟨10000, 1, 10, ⟨1⟩, 1⟩, by norm_num⟩
  formula s _ := 27 / 1000 * s.reynolds ^ (4 / 5 : ℝ) * s.prandtl ^ (1 / 3 : ℝ) *
    s.viscosityRatio ^ (7 / 50 : ℝ)

/-- The viscosity ratio reaches the formula: two large-property-variation requests with identical
`Re`, `Pr`, `L / D` and `ΔT` but viscosity ratios `1` and `2` are both valid for the Sieder-Tate
record and give different Nusselt numbers, the larger at the ratio `2`; the Dittus-Boelter record,
calibrated for small to moderate property variation, does not apply to them. -/
example :
    ∃ (h1 : siederTate.Applies { heatingRequest with propertyVariation := PropertyVariation.large })
      (h2 : siederTate.Applies
        { heatingRequest with propertyVariation := PropertyVariation.large, viscosityRatio := 2 }),
      siederTate.nusselt _ h1 < siederTate.nusselt _ h2 ∧
        ∀ m, ¬ (dittusBoelter m).Applies
          { heatingRequest with
            propertyVariation := PropertyVariation.large, viscosityRatio := 2 } := by
  have h1 : siederTate.Applies
      { heatingRequest with propertyVariation := PropertyVariation.large } := by
    simp only [siederTate, NusseltCorrelation.Applies, heatingRequest, Set.mem_ofPred_eq]
    norm_num
  have h2 : siederTate.Applies
      { heatingRequest with
        propertyVariation := PropertyVariation.large, viscosityRatio := 2 } := by
    simp only [siederTate, NusseltCorrelation.Applies, heatingRequest, Set.mem_ofPred_eq]
    norm_num
  refine ⟨h1, h2, ?_, fun m h => ?_⟩
  · change 27 / 1000 * (100000 : ℝ) ^ (4 / 5 : ℝ) * (1 : ℝ) ^ (1 / 3 : ℝ) * (1 : ℝ) ^ (7 / 50 : ℝ) <
      27 / 1000 * (100000 : ℝ) ^ (4 / 5 : ℝ) * (1 : ℝ) ^ (1 / 3 : ℝ) * (2 : ℝ) ^ (7 / 50 : ℝ)
    have hpos : 0 < 27 / 1000 * (100000 : ℝ) ^ (4 / 5 : ℝ) * (1 : ℝ) ^ (1 / 3 : ℝ) := by
      positivity
    have hlt : (1 : ℝ) ^ (7 / 50 : ℝ) < (2 : ℝ) ^ (7 / 50 : ℝ) := by
      rw [Real.one_rpow]
      exact Real.one_lt_rpow (by norm_num) (by norm_num)
    exact mul_lt_mul_of_pos_left hlt hpos
  · cases m <;> exact absurd h.2.2.2.1 (by simp [dittusBoelter, powerLawCorrelation])

/-- The published bounds are inclusive: the heated flow at the upper Prandtl endpoint `Pr = 160`
and at the lower corner `Re = 10000`, `Pr = 7 / 10`, `L / D = 10` is a valid request. -/
example :
    (dittusBoelter .heating).Applies { heatingRequest with prandtl := 160 } ∧
      (dittusBoelter .heating).Applies
        { heatingRequest with reynolds := 10000, prandtl := 7 / 10, lengthRatio := 10 } := by
  constructor <;>
    simp only [dittusBoelter, powerLawCorrelation, NusseltCorrelation.Applies, heatingRequest,
      Set.mem_ofPred_eq, ThermalMode.Holds] <;>
    norm_num

/-- The guard and the power-law chain at the heated flow: the domain makes `Re` and `Pr`
positive, `h = Nu k / L` inverts the Nusselt group, and with the guarded Nusselt number the
coefficient is positive and the heat rate at the request's `ΔT` is positive. -/
example :
    (0 < heatingRequest.reynolds ∧ 0 < heatingRequest.prandtl) ∧
      nusseltNumber (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 20⟩ ⟨3 / 5⟩
          (by norm_num) = 230 ∧
      0 < (heatTransferCoefficient
          ((dittusBoelter .heating).nusselt heatingRequest dittusBoelter_applies_heating)
          ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)).val ∧
      SignType.sign (convectiveHeatRate (heatTransferCoefficient
          ((dittusBoelter .heating).nusselt heatingRequest dittusBoelter_applies_heating)
          ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩ heatingRequest.temperatureDifference).val =
        1 := by
  have hchain := powerLawCorrelation_heatRate_sign (by norm_num : (0 : ℝ) < 23 / 1000)
    dittusBoelter_applies_heating (k := ⟨3 / 5⟩) (L := ⟨1 / 20⟩) (A := ⟨1 / 10⟩) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨NusseltCorrelation.applies_pos dittusBoelter_applies_heating,
    nusseltNumber_heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num) (by norm_num),
    hchain.1, hchain.2.trans ?_⟩
  simp [heatingRequest]

end PhyslibExtTest.HeatTransfer.CorrelationDomains
