/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryCounter

set_option autoImplicit false

open Cslib.Algorithms.Lean.BinaryCounter

private def width0 : Vector Bool 0 :=
  ⟨#[], by decide⟩

private def width1False : Vector Bool 1 :=
  ⟨#[false], by decide⟩

private def width1True : Vector Bool 1 :=
  ⟨#[true], by decide⟩

private def width4False : Vector Bool 4 :=
  ⟨#[false, false, false, false], by decide⟩

private def width4True : Vector Bool 4 :=
  ⟨#[true, true, true, true], by decide⟩

private def width4Mixed : Vector Bool 4 :=
  ⟨#[true, false, true, false], by decide⟩

-- These examples exercise the ordinary-import theorem interface. They do not
-- unfold the private reset executor.
example : (reset width0).ret.toList = [] := by
  simp [reset_toList]

example : (reset width0).ret.toList.length = 0 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width0).ret.toList).toNat = 0 :=
  reset_value width0

example : (reset width0).time = 0 :=
  reset_time_zero_width width0

example : (reset width1False).ret.toList = [false] := by
  rw [reset_toList]
  decide

example : (reset width1False).ret.toList.length = 1 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width1False).ret.toList).toNat = 0 :=
  reset_value width1False

example : (reset width1False).time = 0 := by
  rw [reset_time]
  decide

example : (reset width1True).ret.toList = [false] := by
  rw [reset_toList]
  decide

example : (reset width1True).ret.toList.length = 1 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width1True).ret.toList).toNat = 0 :=
  reset_value width1True

example : (reset width1True).time = 1 := by
  rw [reset_time]
  decide

example : (reset width4False).ret.toList = [false, false, false, false] := by
  rw [reset_toList]
  decide

example : (reset width4False).ret.toList.length = 4 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width4False).ret.toList).toNat = 0 :=
  reset_value width4False

example : (reset width4False).time = 0 := by
  rw [reset_time]
  decide

example : (reset width4True).ret.toList = [false, false, false, false] := by
  rw [reset_toList]
  decide

example : (reset width4True).ret.toList.length = 4 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width4True).ret.toList).toNat = 0 :=
  reset_value width4True

example : (reset width4True).time = 4 := by
  rw [reset_time]
  decide

example : (reset width4Mixed).ret.toList = [false, false, false, false] := by
  rw [reset_toList]
  decide

example : (reset width4Mixed).ret.toList.length = 4 := by
  rw [reset_toList]
  decide

example : (BitVec.ofBoolListLE (reset width4Mixed).ret.toList).toNat = 0 :=
  reset_value width4Mixed

example : (reset width4Mixed).time = 2 := by
  rw [reset_time]
  decide

example : (reset (reset width4Mixed).ret).ret = (reset width4Mixed).ret :=
  reset_ret_idempotent width4Mixed

example : (reset (reset width4Mixed).ret).time = 0 :=
  reset_time_after_reset width4Mixed

example : (reset (Vector.replicate 65 false)).ret.toList = List.replicate 65 false := by
  simpa using reset_toList (Vector.replicate 65 false)

example : (reset (Vector.replicate 65 false)).ret.toList.length = 65 := by
  rw [reset_toList]
  simp

example : (BitVec.ofBoolListLE (reset (Vector.replicate 65 false)).ret.toList).toNat = 0 :=
  reset_value (Vector.replicate 65 false)

example : (reset (Vector.replicate 65 false)).time = 0 :=
  reset_time_replicate_false 65

example : (reset (Vector.replicate 65 true)).ret.toList = List.replicate 65 false := by
  simpa using reset_toList (Vector.replicate 65 true)

example : (reset (Vector.replicate 65 true)).ret.toList.length = 65 := by
  rw [reset_toList]
  simp

example : (BitVec.ofBoolListLE (reset (Vector.replicate 65 true)).ret.toList).toNat = 0 :=
  reset_value (Vector.replicate 65 true)

example : (reset (Vector.replicate 65 true)).time = 65 := by
  rw [reset_time, Vector.toList_replicate]
  simp

-- Generic clients cover states returned by increment and run without asking
-- the ordinary importer to evaluate either private executor.
example {k : Nat} (bits : Vector Bool k) :
    (reset (increment bits).ret).ret.toList = List.replicate k false :=
  reset_toList (increment bits).ret

example {k : Nat} (bits : Vector Bool k) :
    (reset (increment bits).ret).ret.toList.length = k := by
  rw [reset_toList, List.length_replicate]

example {k : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (reset (increment bits).ret).ret.toList).toNat = 0 :=
  reset_value (increment bits).ret

example {k n : Nat} (bits : Vector Bool k) :
    (reset (run bits n).ret).ret.toList = List.replicate k false :=
  reset_toList (run bits n).ret

example {k n : Nat} (bits : Vector Bool k) :
    (reset (run bits n).ret).ret.toList.length = k := by
  rw [reset_toList, List.length_replicate]

example {k n : Nat} (bits : Vector Bool k) :
    (BitVec.ofBoolListLE (reset (run bits n).ret).ret.toList).toNat = 0 :=
  reset_value (run bits n).ret

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).time + ((reset bits).ret.toList.map Bool.toNat).sum =
      (bits.toList.map Bool.toNat).sum :=
  reset_potential bits

example {k : Nat} (bits : Vector Bool k) :
    (reset bits).time = ((List.range k).map fun i =>
      if bits.toList.getD i false ≠ (reset bits).ret.toList.getD i false
      then 1 else 0).sum :=
  reset_time_changes bits

example {k : Nat} (bits : Vector Bool k) : (reset bits).time ≤ k :=
  reset_time_le bits

example : (reset width4Mixed).time ≠ 3 := by
  rw [reset_time]
  decide

example : (reset width4Mixed).ret.toList ≠ [true, false, false, false] := by
  rw [reset_toList]
  decide
