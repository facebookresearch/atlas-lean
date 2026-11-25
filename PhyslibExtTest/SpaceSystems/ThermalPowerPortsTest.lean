/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.SpaceSystems.ThermalPowerPorts
import Mathlib.Tactic.IntervalCases

/-!
# Radiator box-trapping checks

Concrete consumers of `PhyslibExt.SpaceSystems.ThermalPowerPorts`
at `C = 2`, `Krad = 1`, `Q = 16` on the box `[1, 2]`: the rate at
the lower end is `15 / 2 ≥ 0`, at the upper end is `0`, the clipped
and physical rates agree at `T = 3 / 2` with value `175 / 32`, and
the global Lipschitz bound holds with constant `16`.

Battery loss heat: the port balance, the nonnegative heat and the
complementary port at `ηc = ηd = 4/5`; a feasible eclipse schedule
with nonzero losses and a mid-eclipse deficit that the terminal
stock does not repair, checked on the mission ledger; the battery
heat in the eclipse-mode gluing; simultaneous charge and discharge,
and a zero discharge efficiency.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Unit-parameter box
- B. Battery loss heat and the mission schedule

## iv. References

None.

## A. Unit-parameter box

-/

/-- Clipped and physical rates agree at `T = 3 / 2`, value
`175 / 32`. -/
example :
    ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 (3 / 2) = 175 / 32 := by
  rw [ThermalPowerPorts.clippedRadiatorRate_eq_of_mem (by norm_num)]
  norm_num [ThermalPowerPorts.radiatorRate]

/-- Inward signs at the box ends and the Lipschitz bound with
constant `16`. -/
example :
    0 ≤ ThermalPowerPorts.radiatorRate 2 1 16 1 ∧
    ThermalPowerPorts.radiatorRate 2 1 16 2 ≤ 0 ∧
    |ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 0 -
      ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 3| ≤ 16 * |0 - 3| :=
  ⟨ThermalPowerPorts.radiatorRate_nonneg_at_min (C := 2) (Krad := 1) (Q := 16)
     (Tmin := 1) (by norm_num) (by norm_num),
   ThermalPowerPorts.radiatorRate_nonpos_at_max (C := 2) (Krad := 1) (Q := 16)
     (Tmax := 2) (by norm_num) (by norm_num),
   by
     have h := (ThermalPowerPorts.clippedRadiatorRate_lipschitzWith (C := 2)
       (Krad := 1) (Q := 16) (Tmin := 1) (Tmax := 2) (by norm_num)
       (by norm_num) (by norm_num) (by norm_num)).dist_le_mul 0 3
     rw [Real.dist_eq, Real.dist_eq] at h
     calc |ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 0 -
           ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 3|
         ≤ 1 * (4 * 2 ^ 3) / 2 * |(0 : ℝ) - 3| := h
       _ = 16 * |(0 : ℝ) - 3| := by norm_num⟩

/-- The constant equilibrium trajectory `T ≡ 2` (where
`radiatorRate 2 1 16 2 = 0`) is trapped in the box `[1, 2]`. -/
example :
    ∀ t : ℝ, 0 ≤ t → (fun _ : ℝ => (2 : ℝ)) t ∈ Set.Icc 1 2 :=
  fun t ht =>
    ThermalPowerPorts.radiator_solution_trapped (C := 2) (Krad := 1) (Q := 16)
      (Tmin := 1) (Tmax := 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (fun s _ => by
        have h0 : ThermalPowerPorts.radiatorRate 2 1 16 2 = 0 := by
          norm_num [ThermalPowerPorts.radiatorRate]
        rw [h0]
        exact (hasDerivAt_const s (2 : ℝ)).hasDerivWithinAt)
      (by norm_num) ht

/-- The global existence API at the same unit parameters: from
`T0 = 3 / 2` there is a trajectory starting at `3 / 2`, trapped
in `[1, 2]` at `t = 1`, and solving the physical field there. -/
example :
    ∃ T : ℝ → ℝ, T 0 = 3 / 2 ∧ T 1 ∈ Set.Icc 1 2 ∧
      HasDerivAt T (ThermalPowerPorts.radiatorRate 2 1 16 (T 1)) 1 ∧
      HasDerivAt T
        (ThermalPowerPorts.clippedRadiatorRate 2 1 16 1 2 (T (-1))) (-1) := by
  obtain ⟨T, hT0, hclip, htrap⟩ :=
    ThermalPowerPorts.radiator_solution_exists_trapped (C := 2) (Krad := 1)
      (Q := 16) (Tmin := 1) (Tmax := 2) (T0 := 3 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  refine ⟨T, hT0, (htrap 1 (by norm_num)).1, (htrap 1 (by norm_num)).2, ?_⟩
  exact hclip (-1)

/-- Eclipse gluing at unit parameters: two switches (times
`0, 1, 2`), constant temperature `3 / 2`, per-mode forcing
`Q j = (3 / 2) ^ 4` chosen so the radiator rate vanishes. The
glued solution is continuous on `[0, 2]`, trapped in `[1, 2]`,
and its integral form on the first piece is `0 = 0`. -/
example :
    ContinuousOn (fun _ : ℝ => (3 / 2 : ℝ)) (Set.Icc 0 2) ∧
      (fun _ : ℝ => (3 / 2 : ℝ)) (1 : ℝ) ∈ Set.Icc 1 2 ∧
      ((3 / 2 : ℝ) - 3 / 2 =
        ∫ s in (0 : ℝ)..(1 : ℝ),
          ThermalPowerPorts.radiatorRate 2 1 ((3 / 2) ^ 4) (3 / 2)) := by
  have hτ : StrictMono (fun j : ℕ => (j : ℝ)) := by
    intro a b hab
    exact Nat.cast_lt.mpr hab
  have hcont : ∀ j : ℕ, j < 2 →
      ContinuousOn (fun _ : ℝ => (3 / 2 : ℝ))
        (Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ)) :=
    fun j _ => continuousOn_const
  have hode : ∀ j : ℕ, j < 2 → ∀ t : ℝ,
      t ∈ Set.Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ) →
      HasDerivAt (fun _ : ℝ => (3 / 2 : ℝ))
        (ThermalPowerPorts.radiatorRate 2 1 ((3 / 2) ^ 4) (3 / 2)) t := by
    intro j _ t _
    have hrate : ThermalPowerPorts.radiatorRate 2 1 ((3 / 2) ^ 4) (3 / 2) = 0 := by
      unfold ThermalPowerPorts.radiatorRate
      norm_num
    rw [hrate]
    exact hasDerivAt_const t (3 / 2 : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · have h := ThermalPowerPorts.glued_continuous (m := 2) hτ hcont hode
    simpa using h
  · have h := ThermalPowerPorts.glued_trapped (m := 2) hτ hcont hode
      (fun j _ _ t _ => ⟨by norm_num, by norm_num⟩)
      (⟨by norm_num, by norm_num⟩ : (3 / 2 : ℝ) ∈ Set.Icc 1 2)
      (t := 1) (by constructor <;> norm_num)
    exact h
  · have h := ThermalPowerPorts.glued_integral_on_piece (C := 2) (Krad := 1)
      (m := 2) (by norm_num) hτ hcont hode (j := 0) (by norm_num) (t := 1)
      (by constructor <;> norm_num)
    simpa [ThermalPowerPorts.radiatorRate] using h

/-! ## B. Battery loss heat and the mission schedule -/

namespace PhyslibExtTest.SpaceSystems.ThermalPowerPorts

open _root_.ThermalPowerPorts

/-- The port balance, the nonnegative heat and the complementary port at `ηc = ηd = 4/5`:
charging at `100 W` dissipates `20 W`, the heat of a `16 W` discharge is nonnegative, and that
discharge draws `20 W` from storage, the negative part of the terminal power `-16 W` divided by
`ηd`. -/
example :
    batteryLossHeat (4 / 5) (4 / 5) 100 0 = 20 ∧ 0 ≤ batteryLossHeat (4 / 5) (4 / 5) 0 16 ∧
      (4 / 5 : ℝ) * 0 - 16 / (4 / 5) =
        4 / 5 * max ((0 : ℝ) - 16) 0 - max (-((0 : ℝ) - 16)) 0 / (4 / 5) := by
  have hbal := terminalPower_eq_storage_add_loss (4 / 5 : ℝ) (4 / 5) 100 0
  refine ⟨?_, batteryLossHeat_nonneg le_rfl (by norm_num) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩,
    (battery_port_of_complementary (ηc := 4 / 5) (ηd := 4 / 5) le_rfl (by norm_num)
      (by norm_num)).1⟩
  norm_num at hbal
  linarith

/-- Fixture schedule (Wh, W, h): three eclipse intervals discharging `16 W`, then one sunlit
interval charging at `100 W`, each `1 h` long, with `ηc = ηd = 4/5`. Its stored-energy flow is
`-20, -20, -20, 80`. -/
noncomputable def eclipseFixtureFlow : ℕ → ℝ :=
  batteryFlow (4 / 5) (4 / 5) (fun _ => 1) (MissionLedger.listFlow [0, 0, 0, 100])
    (MissionLedger.listFlow [16, 16, 16, 0])

/-- The stored energy of the fixture schedule from the initial energy `E₀`, stepped with the
battery update: `E₀`, `E₀ - 20`, `E₀ - 40`, `E₀ - 60`, `E₀ + 20` after `0, …, 4` intervals. -/
private lemma eclipseFixture_stock (E₀ : ℝ) :
    MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 0 = E₀ ∧
      MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 1 = E₀ - 20 ∧
      MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 2 = E₀ - 40 ∧
      MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 3 = E₀ - 60 ∧
      MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 4 = E₀ + 20 := by
  have hflow : (fun _ : Unit => eclipseFixtureFlow) () =
      batteryFlow (4 / 5) (4 / 5) (fun _ => 1) (MissionLedger.listFlow [0, 0, 0, 100])
        (MissionLedger.listFlow [16, 16, 16, 0]) := rfl
  have s0 : MissionLedger.stock (fun _ : Unit => E₀) (fun _ => eclipseFixtureFlow) () 0 = E₀ :=
    MissionLedger.stock_zero _ _ _
  have s1 := stock_batteryFlow_succ (s₀ := fun _ : Unit => E₀)
    (flow := fun _ : Unit => eclipseFixtureFlow) (e := ()) hflow 0
  have s2 := stock_batteryFlow_succ (s₀ := fun _ : Unit => E₀)
    (flow := fun _ : Unit => eclipseFixtureFlow) (e := ()) hflow 1
  have s3 := stock_batteryFlow_succ (s₀ := fun _ : Unit => E₀)
    (flow := fun _ : Unit => eclipseFixtureFlow) (e := ()) hflow 2
  have s4 := stock_batteryFlow_succ (s₀ := fun _ : Unit => E₀)
    (flow := fun _ : Unit => eclipseFixtureFlow) (e := ()) hflow 3
  norm_num [MissionLedger.listFlow] at s1 s2 s3 s4
  refine ⟨s0, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- A feasible eclipse schedule with nonzero losses: from `100 Wh` the stored energy runs
`100, 80, 60, 40, 120`, inside the floor `20 + 10` (reserve) and the capacity `200` at every
prefix; the charge interval dissipates `20 W` and each discharge interval `4 W`. -/
example :
    MissionLedger.PrefixFeasible (fun _ : Unit => 20) (fun _ => 200) (fun _ => 10) (fun _ => 100)
        (fun _ => eclipseFixtureFlow) 4 ∧
      batteryLossHeat (4 / 5) (4 / 5) 100 0 = 20 ∧ batteryLossHeat (4 / 5) (4 / 5) 0 16 = 4 := by
  have hbal₁ := terminalPower_eq_storage_add_loss (4 / 5 : ℝ) (4 / 5) 100 0
  have hbal₂ := terminalPower_eq_storage_add_loss (4 / 5 : ℝ) (4 / 5) 0 16
  obtain ⟨s0, s1, s2, s3, s4⟩ := eclipseFixture_stock 100
  refine ⟨?_, ?_, ?_⟩
  · intro i t ht
    cases i
    interval_cases t
    · rw [s0]; norm_num
    · rw [s1]; norm_num
    · rw [s2]; norm_num
    · rw [s3]; norm_num
    · rw [s4]; norm_num
  · norm_num at hbal₁
    linarith
  · norm_num at hbal₂
    linarith

/-- A deficit in the middle of the eclipse is not repaired by a positive terminal stock: from
`60 Wh` the stored energy runs `60, 40, 20, 0, 80`; the terminal stock `80` passes the floor
`30` and the capacity, but the prefix stock `20` after the second eclipse interval does not. -/
example :
    (30 : ℝ) ≤ MissionLedger.stock (fun _ : Unit => 60) (fun _ => eclipseFixtureFlow) () 4 ∧
      MissionLedger.stock (fun _ : Unit => 60) (fun _ => eclipseFixtureFlow) () 4 ≤ 200 ∧
      ¬ MissionLedger.PrefixFeasible (fun _ : Unit => 20) (fun _ => 200) (fun _ => 10)
        (fun _ => 60) (fun _ => eclipseFixtureFlow) 4 := by
  have hflow : (fun _ : Unit => eclipseFixtureFlow) () =
      batteryFlow (4 / 5) (4 / 5) (fun _ => 1) (MissionLedger.listFlow [0, 0, 0, 100])
        (MissionLedger.listFlow [16, 16, 16, 0]) := rfl
  obtain ⟨-, -, -, -, s4⟩ := eclipseFixture_stock 60
  refine ⟨by rw [s4]; norm_num, by rw [s4]; norm_num, fun h => ?_⟩
  have h2 := (prefixFeasible_battery (flow := fun _ : Unit => eclipseFixtureFlow) (e := ()) hflow h
    (t := 2) (by norm_num)).1
  norm_num [Finset.sum_range_succ, MissionLedger.listFlow] at h2

/-- The battery heat in the eclipse-mode gluing: on the partition `0 < 1 < 2` with `C = 1` and
`Krad = 24`, mode `0` discharges `16 W` (heat `4 W`) beside the environmental input `20 W` and
mode `1` charges at `100 W` (heat `20 W`) beside `4 W`, so both total heat inputs are `24 W` and
the constant temperature `1` solves both modes. It is continuous on `[0, 2]`, satisfies the
integral form on the second piece, and the lower inward sign at `Tmin = 3/4` survives the added
heat. -/
example :
    ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc 0 2) ∧
      (1 : ℝ) - 1 = ∫ s in (1 : ℝ)..2,
        radiatorRate 1 24 ((20 - 16 * 1) + batteryLossHeat (4 / 5) (4 / 5) (100 * 1) (16 - 16 * 1))
          ((fun _ : ℝ => (1 : ℝ)) s) ∧
      0 ≤ 20 + batteryLossHeat (4 / 5) (4 / 5) 0 16 - 24 * (3 / 4) ^ 4 := by
  have hτ : StrictMono (fun j : ℕ => (j : ℝ)) := fun a b hab => Nat.cast_lt.mpr hab
  have hrate : ∀ j : ℕ, j < 2 →
      radiatorRate 1 24 ((20 - 16 * (j : ℝ)) +
        batteryLossHeat (4 / 5) (4 / 5) (100 * (j : ℝ)) (16 - 16 * (j : ℝ))) 1 = 0 := by
    intro j hj
    interval_cases j <;> norm_num [radiatorRate, batteryLossHeat]
  have hcont : ∀ j : ℕ, j < 2 →
      ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ)) :=
    fun j _ => continuousOn_const
  have hode : ∀ j : ℕ, j < 2 → ∀ t : ℝ, t ∈ Set.Ioo (j : ℝ) ((j + 1 : ℕ) : ℝ) →
      HasDerivAt (fun _ : ℝ => (1 : ℝ))
        (radiatorRate 1 24 ((20 - 16 * (j : ℝ)) +
          batteryLossHeat (4 / 5) (4 / 5) (100 * (j : ℝ)) (16 - 16 * (j : ℝ)))
          ((fun _ : ℝ => (1 : ℝ)) t)) t := by
    intro j hj t _
    rw [hrate j hj]
    exact hasDerivAt_const t 1
  obtain ⟨hc, hint⟩ := batteryHeat_glued (C := 1) (Krad := 24) (ηc := 4 / 5) (ηd := 4 / 5)
    (m := 2) (Qenv := fun j => 20 - 16 * (j : ℝ)) (Pc := fun j => 100 * (j : ℝ))
    (Pd := fun j => 16 - 16 * (j : ℝ)) one_pos hτ hcont hode
  refine ⟨by simpa using hc, ?_, ?_⟩
  · simpa using hint 1 (by norm_num) 2 (by constructor <;> norm_num)
  · exact batteryLossHeat_lower_sign le_rfl (by norm_num) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- Complementarity matters: charging and discharging `1 W` at once with `ηc = ηd = 1/2` has
zero net terminal power, yet dissipates `3/2 W` and drains `3/2 Wh` from storage in `1 h`, while
the idle battery dissipates nothing. -/
example :
    batteryLossHeat (1 / 2) (1 / 2) 1 1 = 3 / 2 ∧
      batteryFlow (1 / 2) (1 / 2) (fun _ => 1) (fun _ => 1) (fun _ => 1) 0 = -3 / 2 ∧
      batteryLossHeat (1 / 2) (1 / 2) 0 0 = 0 := by
  have hbal₁ := terminalPower_eq_storage_add_loss (1 / 2 : ℝ) (1 / 2) 1 1
  have hbal₀ := terminalPower_eq_storage_add_loss (1 / 2 : ℝ) (1 / 2) 0 0
  refine ⟨?_, ?_, ?_⟩
  · norm_num at hbal₁
    linarith
  · norm_num [batteryFlow]
  · norm_num at hbal₀
    linarith

/-- The efficiency bound `0 < ηd` cannot be dropped: at `ηd = 0` division by zero gives a
discharge that draws nothing from storage and a negative "heat" `-1` for `Pd = 1`. -/
example :
    batteryFlow (1 / 2) 0 (fun _ => 1) (fun _ => 0) (fun _ => 1) 0 = 0 ∧
      batteryLossHeat (1 / 2) 0 0 1 = -1 := by
  refine ⟨?_, ?_⟩ <;> norm_num [batteryFlow, batteryLossHeat]

end PhyslibExtTest.SpaceSystems.ThermalPowerPorts
