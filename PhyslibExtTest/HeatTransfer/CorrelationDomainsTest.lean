/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.HeatTransfer.CorrelationDomains
import Mathlib.Tactic.NormNum

/-!
# Range-guarded correlation checks

Concrete consumer of `PhyslibExt.HeatTransfer.CorrelationDomains`: the
Dittus-Boelter correlation for heating, recorded with its published
domain `Re ≥ 10000`, `0.6 ≤ Pr ≤ 160` and the local tag. A test fluid
with `Re = 100000` and `Pr = 1` lies in the domain and gives `Nu = 230`,
`h = 2760` for `k = 3 / 5` and `D = 1 / 20`, and on `A = 1 / 10` the
heat rate `±2760` for `ΔT = ±10`. Values outside the domain and a
surface-averaged request are rejected.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section A defines the
Dittus-Boelter record it checks.

## iii. Table of contents

- A. The Dittus-Boelter correlation

## iv. References

- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine,
  *Fundamentals of Heat and Mass Transfer*, Wiley, chapter 8 (the
  Dittus-Boelter correlation and its range).
-/

@[expose] public section

namespace PhyslibExtTest.HeatTransfer.CorrelationDomains

open Dimension Units.QuantityDimensions Units.EngineeringQuantities EngineeringScaling
open _root_.CorrelationDomains

/-! ## A. The Dittus-Boelter correlation -/

/-- The Dittus-Boelter correlation for heating, `Nu = 0.023 Re ^ (4/5) Pr ^ (2/5)`, local value
for fully developed turbulent flow in a smooth circular tube, with the published domain
`Re ≥ 10000`, `0.6 ≤ Pr ≤ 160`. -/
noncomputable def dittusBoelterHeating : NusseltCorrelation :=
  powerLawCorrelation (23 / 1000) (4 / 5) (2 / 5)
    "Dittus-Boelter (heating), in Incropera et al., Fundamentals of Heat and Mass Transfer"
    "fully developed turbulent flow in a smooth circular tube, L / D at least 10"
    "mean (bulk) fluid temperature"
    AveragingTag.localValue (Set.Ici 10000 ×ˢ Set.Icc (3 / 5) 160)
    (fun p hp => ⟨by linarith [hp.1.out], by linarith [hp.2.1]⟩)
    ⟨(10000, 1), ⟨le_refl _, by norm_num, by norm_num⟩⟩

/-- The test fluid's `(Re, Pr) = (100000, 1)` is a valid local request for the correlation. -/
lemma dittusBoelter_applies :
    dittusBoelterHeating.Applies AveragingTag.localValue 100000 1 := by
  simp only [dittusBoelterHeating, powerLawCorrelation, NusseltCorrelation.Applies,
    Set.mem_prod, Set.mem_Ici, Set.mem_Icc]
  norm_num

/-- A nonzero `ΔT` in the valid domain: with `ρ = 1000`, `U = 2`, `D = 1 / 20`, `μ = 1 / 1000`,
`c_p = 600` and `k = 3 / 5` (SI), `Re = 100000` and `Pr = 1`; through the guard the correlation
gives `Nu = 230`, so `h = 2760`; on `A = 1 / 10` the heat rate is `2760` for `ΔT = 10` and
`-2760` for `ΔT = -10`. -/
example :
    reynoldsNumber ⟨1000⟩ ⟨2⟩ ⟨1 / 20⟩ ⟨1 / 1000⟩ (by norm_num) = 100000 ∧
      prandtlNumber ⟨1 / 1000⟩ ⟨600⟩ ⟨3 / 5⟩ (by norm_num) = 1 ∧
      dittusBoelterHeating.nusselt AveragingTag.localValue 100000 1 dittusBoelter_applies =
        230 ∧
      (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)).val = 2760 ∧
      (convectiveHeatRate (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩
        ⟨10⟩).val = 2760 ∧
      (convectiveHeatRate (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩
        ⟨-10⟩).val = -2760 := by
  have h1 : (100000 : ℝ) ^ (4 / 5 : ℝ) = 10000 := by
    rw [show (100000 : ℝ) = 10 ^ (5 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reynoldsNumber_val]; norm_num
  · rw [prandtlNumber_val]; norm_num
  · rw [show dittusBoelterHeating.nusselt AveragingTag.localValue 100000 1 dittusBoelter_applies =
        23 / 1000 * (100000 : ℝ) ^ (4 / 5 : ℝ) * (1 : ℝ) ^ (2 / 5 : ℝ) from
      powerLawCorrelation_nusselt dittusBoelter_applies, h1, Real.one_rpow]
    norm_num
  · simp only [heatTransferCoefficient]; norm_num
  · rw [convectiveHeatRate_val]; simp only [heatTransferCoefficient]; norm_num
  · rw [convectiveHeatRate_val]; simp only [heatTransferCoefficient]; norm_num

/-- Rejections: `Re = 5000` and `Pr = 1 / 2` lie outside the domain, and a surface-averaged
request does not match the local correlation. -/
example :
    ¬ dittusBoelterHeating.Applies AveragingTag.localValue 5000 1 ∧
      ¬ dittusBoelterHeating.Applies AveragingTag.localValue 100000 (1 / 2) ∧
      ¬ dittusBoelterHeating.Applies AveragingTag.surfaceAverage 100000 1 := by
  simp only [dittusBoelterHeating, powerLawCorrelation, NusseltCorrelation.Applies,
    Set.mem_prod, Set.mem_Ici, Set.mem_Icc]
  norm_num

/-- The guard and the power-law chain at the fixture data: the domain makes `Re` and `Pr`
positive, `h = Nu k / L` inverts the Nusselt group, and with the guarded Nusselt number the
coefficient is positive and `Q` has the sign of `ΔT = -10`. -/
example :
    (0 < (100000 : ℝ) ∧ 0 < (1 : ℝ)) ∧
      nusseltNumber (heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 20⟩ ⟨3 / 5⟩
          (by norm_num) = 230 ∧
      0 < (heatTransferCoefficient
          (dittusBoelterHeating.nusselt AveragingTag.localValue 100000 1 dittusBoelter_applies)
          ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)).val ∧
      SignType.sign (convectiveHeatRate (heatTransferCoefficient
          (dittusBoelterHeating.nusselt AveragingTag.localValue 100000 1 dittusBoelter_applies)
          ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num)) ⟨1 / 10⟩ ⟨-10⟩).val = SignType.sign (-10 : ℝ) :=
  ⟨NusseltCorrelation.applies_pos dittusBoelter_applies,
    nusseltNumber_heatTransferCoefficient 230 ⟨3 / 5⟩ ⟨1 / 20⟩ (by norm_num) (by norm_num),
    powerLawCorrelation_heatRate_sign (by norm_num) dittusBoelter_applies (by norm_num)
      (by norm_num) (by norm_num) ⟨-10⟩⟩

end PhyslibExtTest.HeatTransfer.CorrelationDomains
