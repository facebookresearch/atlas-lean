/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Thermodynamics.RenewableEnergyPorts

/-!
# Solar-thermal receiver and wind power-curve checks

Concrete consumers of
`PhyslibExt.Thermodynamics.RenewableEnergyPorts`: a numeric receiver
with `Ta = 300`, `G = 1000`, `α = 1`, `U = 0`, `K = 1`, whose
stagnation temperature solves `T^4 - 300^4 = 1000`, and the endpoint
values of the ideal objective.

For the wind power curve (section B): an example `2 MW` curve on a record with operating and
shutdown intervals (delivered energy `1.2 · 10⁷ W h`, capacity factor `1/2`), two turbines whose
peaks fall in different intervals, the active Betz clip at `8 m/s` and the cut-out endpoint; the
energy and capacity-factor bounds applied to that record, the Betz-optimal disk at the cap, and the
lower clip of a negative supplied curve.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Section B defines the example curve and the Betz-optimal
disk its checks use.

## iii. Table of contents

- A. Numeric receiver stagnation and endpoints
- B. Wind power curve and finite-time energy

## iv. References

- `PhyslibExt.Thermodynamics.RenewableEnergyPorts`
-/

/-- Existence and uniqueness of the numeric stagnation temperature,
with the defining balance. -/
example : ∃! Tstag : ℝ, (300 : ℝ) < Tstag ∧
    RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000 :=
  RenewableEnergyPorts.receiver_stagnationTemperature (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At ambient the loss is zero and the ideal objective vanishes at
both endpoints for any stagnation temperature. -/
example (Tstag : ℝ) (hT : Tstag ≠ 0)
    (hstag : RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000) :
    RenewableEnergyPorts.receiverLoss 0 1 300 300 = 0 ∧
      RenewableEnergyPorts.receiverObjective 1 1000 0 1 300 Tstag = 0 :=
  ⟨RenewableEnergyPorts.receiverLoss_ambient 0 1 300,
   (RenewableEnergyPorts.receiver_objective_endpoints (by norm_num)
     (by norm_num) hT hstag).2⟩

/-- Concrete definition check: the stagnation balance for these
parameters is the expanded polynomial equation
`Tstag^4 - 300^4 = 1000`, read directly off `receiverLoss`. -/
example (Tstag : ℝ)
    (hstag : RenewableEnergyPorts.receiverLoss 0 1 300 Tstag = 1 * 1000) :
    Tstag ^ 4 - 300 ^ 4 = 1000 := by
  simpa [RenewableEnergyPorts.receiverLoss] using hstag

/-- Concrete efficiency evaluation at ambient: at `T = Ta = 300`
the loss vanishes, so `receiverEfficiency 1 1000 0 1 300 300`
is `(1000 - 0) / 1000 = 1`, read directly off the definition. -/
example : RenewableEnergyPorts.receiverEfficiency 1 1000 0 1 300 300 = 1 := by
  simp [RenewableEnergyPorts.receiverEfficiency,
    RenewableEnergyPorts.receiverLoss]

/-! ## B. Wind power curve and finite-time energy -/

@[expose] public section

namespace RenewableEnergyPortsTest

open RenewableEnergyPorts

/-- An example `2 MW` curve in SI units: cut-in `3 m/s`, rated `12 m/s`, cut-out `25 m/s`, rated
power `2 · 10⁶ W`, air density `1.225 kg/m³`, swept area `5000 m²`, and a supplied partial-load
calibration rising linearly from `0` at cut-in to the rated power at the rated speed. -/
noncomputable def exampleCurve : WindPowerCurve where
  uCutIn := 3
  uRated := 12
  uCutOut := 25
  pRated := 2000000
  ρ := 49 / 40
  A := 5000
  operating := fun U => 2000000 * (U - 3) / 9
  cutIn_nonneg := by norm_num
  cutIn_lt_rated := by norm_num
  rated_lt_cutOut := by norm_num
  pRated_pos := by norm_num
  ρ_nonneg := by norm_num
  A_nonneg := by norm_num

private lemma example_betz_rated :
    exampleCurve.pRated ≤ betzPower exampleCurve.ρ exampleCurve.A exampleCurve.uRated := by
  have hρ : exampleCurve.ρ = (49 / 40 : ℝ) := rfl
  have hA : exampleCurve.A = (5000 : ℝ) := rfl
  have hU : exampleCurve.uRated = (12 : ℝ) := rfl
  have hP : exampleCurve.pRated = (2000000 : ℝ) := rfl
  rw [hρ, hA, hU, hP]
  unfold betzPower FluidDynamics.RotorPorts.powerNormalization
  norm_num

private lemma example_power12 : exampleCurve.power 12 = 2000000 := by
  have h1 : exampleCurve.uRated = (12 : ℝ) := rfl
  have h2 : exampleCurve.uCutOut = (25 : ℝ) := rfl
  have hmem : (12 : ℝ) ∈ Set.Icc exampleCurve.uRated exampleCurve.uCutOut := by
    rw [h1, h2]
    exact ⟨le_rfl, by norm_num⟩
  obtain ⟨-, hplat⟩ := WindPowerCurve.power_eq_of_rated exampleCurve hmem
  exact hplat example_betz_rated

private lemma example_power30 : exampleCurve.power 30 = 0 :=
  WindPowerCurve.power_eq_zero_of_cutOut_lt _ (by change (25 : ℝ) < 30; norm_num)

private lemma example_power2 : exampleCurve.power 2 = 0 :=
  WindPowerCurve.power_eq_zero_of_lt_cutIn _ (by change (2 : ℝ) < 3; norm_num)

private lemma example_power25 : exampleCurve.power 25 = 2000000 := by
  have h1 : exampleCurve.uRated = (12 : ℝ) := rfl
  have h2 : exampleCurve.uCutOut = (25 : ℝ) := rfl
  have hmem : (25 : ℝ) ∈ Set.Icc exampleCurve.uRated exampleCurve.uCutOut := by
    rw [h1, h2]
    exact ⟨by norm_num, le_rfl⟩
  obtain ⟨-, hplat⟩ := WindPowerCurve.power_eq_of_rated exampleCurve hmem
  exact hplat example_betz_rated

private lemma example_power26 : exampleCurve.power 26 = 0 :=
  WindPowerCurve.power_eq_zero_of_cutOut_lt _ (by change (25 : ℝ) < 26; norm_num)

private lemma example_betz8 : betzPower exampleCurve.ρ exampleCurve.A 8 = 25088000 / 27 := by
  have hρ : exampleCurve.ρ = (49 / 40 : ℝ) := rfl
  have hA : exampleCurve.A = (5000 : ℝ) := rfl
  rw [hρ, hA]
  unfold betzPower FluidDynamics.RotorPorts.powerNormalization
  norm_num

private lemma example_oper8_lt :
    betzPower exampleCurve.ρ exampleCurve.A 8 < exampleCurve.operating 8 := by
  have hop : exampleCurve.operating 8 = 2000000 * (8 - 3) / 9 := rfl
  rw [example_betz8, hop]
  norm_num

private lemma example_power8 : exampleCurve.power 8 = 25088000 / 27 := by
  have h1 : exampleCurve.uCutIn = (3 : ℝ) := rfl
  have h2 : exampleCurve.uRated = (12 : ℝ) := rfl
  have hmem : (8 : ℝ) ∈ Set.Ico exampleCurve.uCutIn exampleCurve.uRated := by
    rw [h1, h2]
    exact ⟨by norm_num, by norm_num⟩
  rw [WindPowerCurve.power_eq_of_partialLoad exampleCurve hmem]
  unfold WindPowerCurve.clip
  have hP : exampleCurve.pRated = (2000000 : ℝ) := rfl
  rw [hP, example_betz8]
  have hop : exampleCurve.operating 8 = (10000000 / 9 : ℝ) := by
    have h : exampleCurve.operating 8 = 2000000 * (8 - 3) / 9 := rfl
    rw [h]
    norm_num
  rw [hop, min_eq_right (by norm_num : (25088000 / 27 : ℝ) ≤ 2000000),
    min_eq_right (by norm_num : (25088000 / 27 : ℝ) ≤ 10000000 / 9),
    max_eq_right (by norm_num : (0 : ℝ) ≤ 25088000 / 27)]

/-- **Operating and shutdown intervals.** The example curve on a `12 h` record: `6 h` at `12 m/s`
(rated, `2 · 10⁶ W`), `2 h` at `30 m/s` (above cut-out, shut down) and `4 h` at `2 m/s` (below
cut-in): the delivered energy is `1.2 · 10⁷ W h` and the capacity factor `1/2`. -/
example :
    exampleCurve.power 12 = 2000000 ∧ exampleCurve.power 30 = 0 ∧ exampleCurve.power 2 = 0 ∧
      windEnergy exampleCurve (MissionLedger.listFlow [12, 30, 2])
        (MissionLedger.listFlow [6, 2, 4]) 3 = 12000000 ∧
      capacityFactor exampleCurve (MissionLedger.listFlow [12, 30, 2])
        (MissionLedger.listFlow [6, 2, 4]) 3 = 1 / 2 := by
  have hE : windEnergy exampleCurve (MissionLedger.listFlow [12, 30, 2])
      (MissionLedger.listFlow [6, 2, 4]) 3 = 12000000 := by
    have f0 : MissionLedger.listFlow [12, 30, 2] 0 = 12 := rfl
    have f1 : MissionLedger.listFlow [12, 30, 2] 1 = 30 := rfl
    have f2 : MissionLedger.listFlow [12, 30, 2] 2 = 2 := rfl
    have g0 : MissionLedger.listFlow [6, 2, 4] 0 = 6 := rfl
    have g1 : MissionLedger.listFlow [6, 2, 4] 1 = 2 := rfl
    have g2 : MissionLedger.listFlow [6, 2, 4] 2 = 4 := rfl
    simp only [windEnergy, MissionLedger.stock]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [zero_add]
    rw [f0, f1, f2, g0, g1, g2, example_power12, example_power30, example_power2]
    norm_num
  have hT : elapsedTime (MissionLedger.listFlow [6, 2, 4]) 3 = 12 := by
    have g0 : MissionLedger.listFlow [6, 2, 4] 0 = 6 := rfl
    have g1 : MissionLedger.listFlow [6, 2, 4] 1 = 2 := rfl
    have g2 : MissionLedger.listFlow [6, 2, 4] 2 = 4 := rfl
    simp only [elapsedTime]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    simp only [zero_add]
    rw [g0, g1, g2]
    norm_num
  refine ⟨example_power12, example_power30, example_power2, hE, ?_⟩
  unfold capacityFactor
  have hP : exampleCurve.pRated = (2000000 : ℝ) := rfl
  rw [hE, hT, hP]
  norm_num

/-- **Peaks need not be simultaneous.** Two turbines with the example curve over two intervals, the
first at `12 m/s` then `30 m/s`, the second at `2 m/s` then `12 m/s`, each peak at `2 · 10⁶ W` but
in different intervals: the largest simultaneous output is `2 · 10⁶ W`, the sum of the individual
maxima `4 · 10⁶ W`. -/
example :
    max (exampleCurve.power 12 + exampleCurve.power 2)
        (exampleCurve.power 30 + exampleCurve.power 12) = 2000000 ∧
      max (exampleCurve.power 12) (exampleCurve.power 30) +
        max (exampleCurve.power 2) (exampleCurve.power 12) = 4000000 := by
  have e1 : (2000000 : ℝ) + 0 = 2000000 := by norm_num
  have e2 : (0 : ℝ) + 2000000 = 2000000 := by norm_num
  rw [example_power12, example_power30, example_power2, e1, e2]
  constructor
  · exact max_eq_left le_rfl
  · rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 2000000),
      max_eq_right (by norm_num : (0 : ℝ) ≤ 2000000)]
    norm_num

/-- **Betz clip and the cut-out endpoint.** At `8 m/s` the supplied calibration `10⁷/9 W` exceeds
the Betz power `25088000/27 W` of the example rotor, and the evaluated power is the Betz power. At
the cut-out speed `25 m/s` the turbine still delivers the rated power; at `26 m/s` it is shut
down. -/
example :
    betzPower exampleCurve.ρ exampleCurve.A 8 = 25088000 / 27 ∧
      betzPower exampleCurve.ρ exampleCurve.A 8 < exampleCurve.operating 8 ∧
      exampleCurve.power 8 = 25088000 / 27 ∧ exampleCurve.power 25 = 2000000 ∧
      exampleCurve.power 26 = 0 := by
  exact ⟨example_betz8, example_oper8_lt, example_power8, example_power25, example_power26⟩

/-- The energy bound at every prefix and the capacity-factor bound apply to the fixture record,
with the nonnegative durations `6, 2, 4 h` and the elapsed time `12 h`. -/
example :
    (∀ t ≤ 3, 0 ≤ windEnergy exampleCurve (MissionLedger.listFlow [12, 30, 2])
        (MissionLedger.listFlow [6, 2, 4]) t ∧
      windEnergy exampleCurve (MissionLedger.listFlow [12, 30, 2])
          (MissionLedger.listFlow [6, 2, 4]) t ≤
        exampleCurve.pRated * elapsedTime (MissionLedger.listFlow [6, 2, 4]) t) ∧
      0 ≤ capacityFactor exampleCurve (MissionLedger.listFlow [12, 30, 2])
        (MissionLedger.listFlow [6, 2, 4]) 3 ∧
      capacityFactor exampleCurve (MissionLedger.listFlow [12, 30, 2])
        (MissionLedger.listFlow [6, 2, 4]) 3 ≤ 1 := by
  have hdt : ∀ k < 3, 0 ≤ MissionLedger.listFlow [6, 2, 4] k := by
    intro k _
    unfold MissionLedger.listFlow
    rcases k with _ | _ | _ | k <;> simp
  refine ⟨fun t ht => windEnergy_nonneg_le exampleCurve _ hdt ht,
    capacityFactor_nonneg_le_one exampleCurve _ hdt ?_⟩
  norm_num [elapsedTime, Finset.sum_range_succ, MissionLedger.listFlow]

/-- The Betz-optimal ideal disk: `ρ = A = 1`, `U∞ = 3`, `U_d = 2`, `U_w = 1`, face pressures `5/2`
and `-3/2`, force `4`. -/
private noncomputable def betzOptimalDisk : FluidDynamics.RotorPorts.ActuatorDisk where
  ρ := 1
  A := 1
  uInf := 3
  uDisk := 2
  uWake := 1
  pAmb := 0
  pUp := 5 / 2
  pDown := -3 / 2
  force := 4

/-- The Betz-optimal disk meets the hypotheses of `extractedPower_le_betzPower` and attains the
cap: its extracted power `8` is `betzPower 1 1 3`, at the induction factor `1/3`. -/
example :
    FluidDynamics.RotorPorts.extractedPower betzOptimalDisk = 8 ∧
      betzPower betzOptimalDisk.ρ betzOptimalDisk.A betzOptimalDisk.uInf = 8 ∧
      FluidDynamics.RotorPorts.inductionFactor betzOptimalDisk = 1 / 3 := by
  have h : betzOptimalDisk.PortLaws :=
    ⟨by norm_num [betzOptimalDisk], by norm_num [betzOptimalDisk],
      by norm_num [betzOptimalDisk], by norm_num [betzOptimalDisk]⟩
  have hb := extractedPower_le_betzPower h (by norm_num [betzOptimalDisk])
    (by norm_num [betzOptimalDisk]) (by norm_num [betzOptimalDisk])
    (by norm_num [betzOptimalDisk])
  have hE : FluidDynamics.RotorPorts.extractedPower betzOptimalDisk = 8 := by
    norm_num [FluidDynamics.RotorPorts.extractedPower, betzOptimalDisk]
  have hB : betzPower betzOptimalDisk.ρ betzOptimalDisk.A betzOptimalDisk.uInf = 8 := by
    norm_num [betzPower, FluidDynamics.RotorPorts.powerNormalization, betzOptimalDisk]
  exact ⟨hE, hB, hb.2.mp (hE.trans hB.symm)⟩

/-- The lower clip: a supplied partial-load curve of `-1 W` everywhere gives `P(5) = 0`. -/
example : ({ exampleCurve with operating := fun _ => -1 } : WindPowerCurve).power 5 = 0 := by
  rw [WindPowerCurve.power_eq_of_partialLoad _
    ⟨by norm_num [exampleCurve], by norm_num [exampleCurve]⟩]
  norm_num [WindPowerCurve.clip, exampleCurve, betzPower,
    FluidDynamics.RotorPorts.powerNormalization]

end RenewableEnergyPortsTest

end
