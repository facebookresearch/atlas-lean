/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Accounting.SalvageFloorDepreciation
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Accounting.SalvageFloorDepreciation

open MathlibExt.Economics.Accounting

/-- Double-declining balance from 1000 with salvage 200: 500, 250, then the floor 200. -/
theorem test_doubleDeclining :
    floorBookValue 1000 200 (fun _ v => v / 2) 1 = 500 ∧
      floorBookValue 1000 200 (fun _ v => v / 2) 2 = 250 ∧
      floorBookValue 1000 200 (fun _ v => v / 2) 3 = 200 ∧
      floorBookValue 1000 200 (fun _ v => v / 2) 4 = 200 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [floorBookValue] <;> norm_num

/-- Starting below salvage, period-0 book value is below salvage, so the start hypothesis is needed. -/
theorem test_start_below_salvage :
    floorBookValue 100 200 (fun _ _ => 0) 0 < 200 := by
  simp only [floorBookValue]
  norm_num

/-- A negative charge raises book value, so nonnegative charges are needed for monotonicity. -/
theorem test_negative_charge_increases :
    floorBookValue 1000 200 (fun _ _ => -10) 0 < floorBookValue 1000 200 (fun _ _ => -10) 1 := by
  simp only [floorBookValue]
  norm_num

/-- Double-declining book value never falls below salvage 200, by `salvage_le_floorBookValue`. -/
theorem test_doubleDeclining_floor_all :
    ∀ n : ℕ, 200 ≤ floorBookValue 1000 200 (fun _ v => v / 2) n := by
  exact fun n => salvage_le_floorBookValue _ (by norm_num) n

/-- A constant charge of 300 never takes book value below salvage 100, by `salvage_le_floorBookValue`. -/
theorem test_constantCharge_floor_all :
    ∀ n : ℕ, 100 ≤ floorBookValue 1000 100 (fun _ _ => 300) n := by
  exact fun n => salvage_le_floorBookValue _ (by norm_num) n

/-- With a constant nonnegative charge, book value never increases, by `floorBookValue_succ_le`. -/
theorem test_constantCharge_step_le :
    ∀ n : ℕ, floorBookValue 1000 100 (fun _ _ => 300) (n + 1) ≤
      floorBookValue 1000 100 (fun _ _ => 300) n := by
  exact fun n => floorBookValue_succ_le (by norm_num) (fun _ _ => by norm_num) n

end MathlibExtTest.Economics.Accounting.SalvageFloorDepreciation
