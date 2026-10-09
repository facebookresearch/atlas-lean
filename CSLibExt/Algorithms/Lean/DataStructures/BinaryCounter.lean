/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Fixed-width binary counter

The low-first binary counter of CLRS, fourth edition, Section 16.1, pages 451-453.
The two executors use canonical `Vector Bool` and CSLib `TimeM`.

## Main statements

Increment has unsigned modular value and exact initial-one-prefix cost. Successive
increments have modular value, exact per-position flip counts from zero, and actual
total cost equal to the sum of those counts. A positive-length zero-start run costs
strictly less than twice its length, and a positive-width run costs at least its length.

## Implementation notes

Each cleared or set existing bit costs one tick. Testing, traversal, conversions,
persistent copying, allocation, machine/word/bit complexity and space are excluded.
Width zero is legal and has zero cost. All-one input wraps without a new high bit.
Proof-only observers and carry machinery remain private.
Authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.BinaryCounter

@[no_expose] private def carry : List Bool → TimeM Nat (List Bool)
  | [] => pure []
  | false :: bits => do
      TimeM.tick 1
      pure (true :: bits)
  | true :: bits => do
      TimeM.tick 1
      let rest ← carry bits
      pure (false :: rest)

private lemma carry_length (bits : List Bool) : (carry bits).ret.length = bits.length := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih => cases bit <;> simp [carry, ih]

private lemma carry_time_le (bits : List Bool) : (carry bits).time ≤ bits.length := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih =>
    cases bit with
    | false => simp [carry]
    | true => simpa [carry, Nat.add_comm] using Nat.add_le_add_left ih 1

private lemma carry_time_eq (bits : List Bool) :
    (carry bits).time = (bits.takeWhile id).length +
      if (bits.takeWhile id).length < bits.length then 1 else 0 := by
  induction bits with
  | nil => simp [carry]
  | cons bit bits ih =>
    cases bit with
    | false => simp [carry]
    | true =>
      simp [carry, ih]
      omega

private lemma carry_value (bits : List Bool) :
    (BitVec.ofBoolListLE (carry bits).ret).toNat =
      ((BitVec.ofBoolListLE bits).toNat + 1) % 2 ^ bits.length := by
  induction bits with
  | nil => simp [carry, BitVec.ofBoolListLE.eq_1]
  | cons bit bits ih =>
    cases bit with
    | false =>
      have bound := (BitVec.ofBoolListLE bits).isLt
      simp only [carry, TimeM.ret_bind, TimeM.ret_pure, List.length_cons,
        BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, Bool.toNat_true, Bool.toNat_false,
        add_zero, Nat.pow_succ]
      symm
      apply Nat.mod_eq_of_lt
      omega
    | true =>
      simp only [carry, TimeM.ret_bind, TimeM.ret_pure, List.length_cons,
        BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, ih, Bool.toNat_false, add_zero,
        Bool.toNat_true, Nat.pow_succ]
      have next : (BitVec.ofBoolListLE bits).toNat * 2 + 1 + 1 =
          ((BitVec.ofBoolListLE bits).toNat + 1) * 2 := by omega
      simpa only [next] using
        (Nat.mul_mod_mul_right 2 ((BitVec.ofBoolListLE bits).toNat + 1) (2 ^ bits.length)).symm

private lemma carry_time_replicate (k : Nat) : (carry (List.replicate k true)).time = k := by
  induction k with
  | zero => simp [carry]
  | succ k ih => simp [carry, List.replicate_succ, ih, Nat.add_comm]

/-- Increment a low-first fixed-width counter, charging one tick per changed existing bit. -/
public def increment {k : Nat} (bits : Vector Bool k) : TimeM Nat (Vector Bool k) :=
  let result := carry bits.toList
  ⟨⟨result.ret.toArray, by
      change (carry bits.toList).ret.toArray.size = k
      simp only [List.size_toArray, carry_length, Vector.length_toList]⟩, result.time⟩

private lemma increment_toList {k : Nat} (bits : Vector Bool k) :
    (increment bits).ret.toList = (carry bits.toList).ret := by
  simp only [increment, Vector.toList_mk]

/-- Increment adds one to the unsigned value modulo the fixed width. -/
public theorem increment_value {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (increment bits).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + 1) % 2 ^ k := by
  rw [increment_toList]
  simpa only [Vector.length_toList] using carry_value bits.toList

/-- The exact increment cost is the initial one-prefix plus a first zero when present. -/
public theorem increment_time {k : Nat} (bits : Vector Bool k) :
    (increment bits).time = (bits.toList.takeWhile id).length +
      if (bits.toList.takeWhile id).length < k then 1 else 0 := by
  simpa only [increment, Vector.length_toList] using carry_time_eq bits.toList

/-- Increment changes at most the fixed number of existing bits. -/
public theorem increment_time_le {k : Nat} (bits : Vector Bool k) :
    (increment bits).time ≤ k := by
  simpa only [increment, Vector.length_toList] using carry_time_le bits.toList

/-- Execute successive increments, each consuming the actual previous returned counter. -/
public def run {k : Nat} (bits : Vector Bool k) : Nat → TimeM Nat (Vector Bool k)
  | 0 => pure bits
  | n + 1 => do
      let previous ← run bits n
      increment previous

/-- A zero-step run returns the full pure input, with zero accumulated cost. -/
public theorem run_zero {k : Nat} (bits : Vector Bool k) :
    run bits 0 = pure bits := by
  simp only [run]

/-- A successor run returns the increment of its actual predecessor state. -/
public theorem run_ret_succ {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).ret = (increment (run bits n).ret).ret := by
  simp only [run, TimeM.ret_bind]

/-- A successor run adds the next increment cost to the actual accumulated cost. -/
public theorem run_time_succ {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (run bits (n + 1)).time =
      (run bits n).time + (increment (run bits n).ret).time := by
  simp only [run, TimeM.time_bind]

/-- An arbitrary initial unsigned value advances by the run length modulo the fixed width. -/
public theorem run_value {k : Nat} (bits : Vector Bool k) (n : Nat) :
    (BitVec.ofBoolListLE (run bits n).ret.toList).toNat =
      ((BitVec.ofBoolListLE bits.toList).toNat + n) % 2 ^ k := by
  induction n with
  | zero =>
    have bound := (BitVec.ofBoolListLE bits.toList).isLt
    simpa [run, Vector.length_toList] using (Nat.mod_eq_of_lt bound).symm
  | succ n ih =>
    rw [run_ret_succ, increment_value, ih, Nat.mod_add_mod]
    rfl

private lemma run_from_zero_value (k n : Nat) :
    (BitVec.ofBoolListLE (run (Vector.replicate k false) n).ret.toList).toNat =
      n % 2 ^ k := by
  have zeros : (BitVec.ofBoolListLE (List.replicate k false)).toNat = 0 := by
    induction k with
    | zero => simp [BitVec.ofBoolListLE.eq_1]
    | succ k ih =>
      simp [List.replicate_succ, BitVec.ofBoolListLE.eq_2, BitVec.toNat_concat, ih]
  rw [run_value, Vector.toList_replicate, zeros]
  simp only [Nat.zero_add]

private lemma run_zero_bit (k n i : Nat) (hi : i < k) :
    (run (Vector.replicate k false) n).ret.toList.getD i false = n.testBit i := by
  rw [← BitVec.getLsbD_ofBoolListLE]
  change (BitVec.ofBoolListLE (run (Vector.replicate k false) n).ret.toList).toNat.testBit i = _
  rw [run_from_zero_value, Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]

private lemma testBit_flip_quotient (n i : Nat) :
    (if n.testBit i ≠ (n + 1).testBit i then 1 else 0) =
      (n + 1) / 2 ^ i - n / 2 ^ i := by
  have hp : 0 < 2 ^ i := Nat.pow_pos (by decide)
  have lower : n / 2 ^ i ≤ (n + 1) / 2 ^ i :=
    Nat.div_le_div_right (by omega)
  have upper : (n + 1) / 2 ^ i ≤ n / 2 ^ i + 1 := by
    have h := Nat.div_le_div_right (c := 2 ^ i)
      (show n + 1 ≤ n + 2 ^ i by omega)
    rwa [Nat.add_div_right n hp] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  by_cases same : (n + 1) / 2 ^ i = n / 2 ^ i
  · simp [same]
  · have step : (n + 1) / 2 ^ i = n / 2 ^ i + 1 := by omega
    rw [step, Nat.add_mod]
    have parity : n / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
    have cases : n / 2 ^ i % 2 = 0 ∨ n / 2 ^ i % 2 = 1 := by omega
    rcases cases with even | odd
    · simp [even]
    · simp [odd]

private lemma run_zero_flip (k n i : Nat) (hi : i < k) :
    (if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
      then 1 else 0) = (n + 1) / 2 ^ i - n / 2 ^ i := by
  rw [run_zero_bit k n i hi, run_zero_bit k (n + 1) i hi]
  exact testBit_flip_quotient n i

/-- A mathematical sum of changes between actual successive returned states. -/
private def bitFlips (k i n : Nat) : Nat :=
  ((List.range n).map fun t =>
    if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
      then 1 else 0).sum

private lemma bitFlips_eq (k i n : Nat) (hi : i < k) : bitFlips k i n = n / 2 ^ i := by
  induction n with
  | zero => simp [bitFlips]
  | succ n ih =>
    have recurrence : bitFlips k i (n + 1) = bitFlips k i n +
        (if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
            (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
          then 1 else 0) := by
      simp [bitFlips, List.range_succ, List.map_append, List.sum_append]
    rw [recurrence, ih, run_zero_flip k n i hi]
    have lower : n / 2 ^ i ≤ (n + 1) / 2 ^ i := Nat.div_le_div_right (by omega)
    omega

/-- Bit `i` changes exactly `n / 2 ^ i` times in an actual zero-start run. -/
public theorem run_bit_flips (k i n : Nat) (hi : i < k) :
    ((List.range n).map fun t =>
      if (run (Vector.replicate k false) t).ret.toList.getD i false ≠
          (run (Vector.replicate k false) (t + 1)).ret.toList.getD i false
        then 1 else 0).sum = n / 2 ^ i := by
  exact bitFlips_eq k i n hi

/-- A mathematical count of differences at paired existing positions. -/
private def changedBits (before after : List Bool) : Nat :=
  (List.zipWith (fun a b => if a ≠ b then 1 else 0) before after).sum

private lemma changedBits_self (bits : List Bool) : changedBits bits bits = 0 := by
  simp [changedBits, List.zipWith_self]

private lemma carry_time_changedBits (bits : List Bool) :
    (carry bits).time = changedBits bits (carry bits).ret := by
  induction bits with
  | nil => simp [carry, changedBits]
  | cons bit bits ih =>
    cases bit with
    | false =>
      change 1 = 1 + changedBits bits bits
      rw [changedBits_self]
    | true =>
      simpa [carry, changedBits] using ih

private lemma changedBits_indexed (before after : List Bool)
    (h : before.length = after.length) :
    changedBits before after = ((List.range before.length).map fun i =>
      if before.getD i false ≠ after.getD i false then 1 else 0).sum := by
  induction before generalizing after with
  | nil =>
    cases after <;> simp_all [changedBits]
  | cons a before ih =>
    cases after with
    | nil => simp at h
    | cons b after =>
      have lengths : before.length = after.length := Nat.succ.inj h
      simp only [changedBits, List.zipWith_cons_cons, List.sum_cons,
        List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.sum_cons, List.getD_cons_zero]
      exact congrArg ((if a ≠ b then 1 else 0) + ·) (ih after lengths)

/-- All-one input realizes the worst-case cost of one flip per existing bit. -/
public theorem increment_time_replicate_true (k : Nat) :
    (increment (Vector.replicate k true)).time = k := by
  simpa only [increment, Vector.toList_replicate] using carry_time_replicate k

private lemma increment_time_changes {k : Nat} (bits : Vector Bool k) :
    (increment bits).time = ((List.range k).map fun i =>
      if bits.toList.getD i false ≠ (increment bits).ret.toList.getD i false
      then 1 else 0).sum := by
  change (carry bits.toList).time = _
  rw [carry_time_changedBits]
  simpa only [increment_toList, Vector.length_toList] using
    changedBits_indexed bits.toList (carry bits.toList).ret (carry_length bits.toList).symm

private lemma bitFlips_succ (k i n : Nat) :
    bitFlips k i (n + 1) = bitFlips k i n +
      if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
        (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
      then 1 else 0 := by
  simp [bitFlips, List.range_succ, List.map_append, List.sum_append]

private lemma run_time_bitFlips (k n : Nat) :
    (run (Vector.replicate k false) n).time =
      ((List.range k).map fun i => bitFlips k i n).sum := by
  induction n with
  | zero => simp [run, bitFlips]
  | succ n ih =>
    rw [run_time_succ, ih, increment_time_changes]
    have counts : ((List.range k).map fun i => bitFlips k i (n + 1)).sum =
        ((List.range k).map fun i => bitFlips k i n +
          if (run (Vector.replicate k false) n).ret.toList.getD i false ≠
            (run (Vector.replicate k false) (n + 1)).ret.toList.getD i false
          then 1 else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact bitFlips_succ k i n
    rw [counts, List.sum_map_add]
    congr 1

private def floorSum (k n : Nat) : Nat :=
  ((List.range k).map fun i => n / 2 ^ i).sum

private lemma run_time_floorSum (k n : Nat) :
    (run (Vector.replicate k false) n).time = floorSum k n := by
  rw [run_time_bitFlips]
  unfold floorSum
  congr 1
  apply List.map_congr_left
  intro i hi
  exact bitFlips_eq k i n (List.mem_range.mp hi)

/-- The actual zero-start run cost is the sum of its existing bits' exact flip counts. -/
public theorem run_time_eq (k n : Nat) :
    (run (Vector.replicate k false) n).time =
      ((List.range k).map fun i => n / 2 ^ i).sum := by
  exact run_time_floorSum k n

private lemma floorSum_zero (k : Nat) : floorSum k 0 = 0 := by
  simp [floorSum]

private lemma floorSum_succ (k n : Nat) :
    floorSum (k + 1) n = n + floorSum k (n / 2) := by
  simp only [floorSum, List.range_succ_eq_map, List.map_cons, List.map_map,
    List.sum_cons, Nat.pow_zero, Nat.div_one]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  change n / 2 ^ (i + 1) = n / 2 / 2 ^ i
  simp only [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

private lemma floorSum_lt (k n : Nat) (hn : 0 < n) : floorSum k n < 2 * n := by
  induction k generalizing n with
  | zero => simp [floorSum]; omega
  | succ k ih =>
    rw [floorSum_succ]
    by_cases h : n / 2 = 0
    · rw [h, floorSum_zero]
      omega
    · have tail := ih (n / 2) (by omega)
      have halves := Nat.div_mul_le_self n 2
      omega

private lemma floorSum_ge (k n : Nat) (hk : 0 < k) : n ≤ floorSum k n := by
  cases k with
  | zero => omega
  | succ k => rw [floorSum_succ]; omega

/-- A positive-length zero-start run costs strictly fewer than twice its length. -/
public theorem run_time_lt (k n : Nat) (hn : 0 < n) :
    (run (Vector.replicate k false) n).time < 2 * n := by
  rw [run_time_floorSum]
  exact floorSum_lt k n hn

/-- A positive-width zero-start run costs at least its length. -/
public theorem run_time_ge (k n : Nat) (hk : 0 < k) :
    n ≤ (run (Vector.replicate k false) n).time := by
  rw [run_time_floorSum]
  exact floorSum_ge k n hk

end Cslib.Algorithms.Lean.BinaryCounter
