/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.HamiltonianCycle.Basic
import Init.Data.Array.Lemmas

/-!
# Private fixed-width decoder refinements

The exact source bit-fold and its coupled selected-event count are inherited from Basic.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

private lemma countedBits_empty_of_le (bits : Array Bool) (stop : Nat)
    (h : stop ≤ bits.size) : countedBits bits stop stop = ⟨0, 0⟩ := by
  simp [countedBits, Array.foldrM, h]
  rfl

private lemma countedBits_list (bits : List Bool) :
    bits.foldrM (fun bit value => do
      TimeM.tick 1
      pure ((if bit then 1 else 0) + 2 * value)) 0 =
    (⟨Nat.ofDigits 2 (bits.map fun bit => if bit then 1 else 0), bits.length⟩ :
      TimeM Nat Nat) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [List.foldrM_cons, ih, List.map_cons, Nat.ofDigits, List.length_cons]
    rfl

lemma countedBits_eq (bits : Array Bool) (start stop : Nat)
    (hstop : stop ≤ start) (hstart : start ≤ bits.size) :
    countedBits bits start stop =
      ⟨Nat.ofDigits 2 ((bits.toList.drop stop).take (start - stop) |>.map
        fun bit => if bit then 1 else 0), start - stop⟩ := by
  unfold countedBits
  rw [Array.foldrM_start_stop, ← Array.foldrM_toList, countedBits_list,
    Array.toList_extract]
  simp only [List.extract, List.length_take, List.length_drop, Array.length_toList]
  congr 1
  omega

lemma countedBits_word (bits : Array Bool) (m w i : Nat)
    (hsize : bits.size = m * w) (hi : i < m) :
    countedBits bits ((i + 1) * w) (i * w) =
      ⟨Nat.ofDigits 2 ((bits.toList.drop (i * w)).take w |>.map
        fun bit => if bit then 1 else 0), w⟩ := by
  have hstart : (i + 1) * w ≤ bits.size := by
    rw [hsize]
    exact Nat.mul_le_mul_right w hi
  have hstop : i * w ≤ (i + 1) * w := Nat.mul_le_mul_right w (Nat.le_succ i)
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left] using
    countedBits_eq bits ((i + 1) * w) (i * w) hstop hstart

end Cslib.Algorithms.Lean.Graph
