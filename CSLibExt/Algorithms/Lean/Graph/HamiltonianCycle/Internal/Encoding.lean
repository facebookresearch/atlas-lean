/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.OfFn

/-!+# Private fixed-width certificate construction

Mathlib `Nat.digitsAppend` supplies canonical padded least-significant-first
digits. Binary conversion and block concatenation preserve those exact words.
-/

namespace Cslib.Algorithms.Lean.Graph

lemma binary_word (w v : Nat) (hv : v < 2 ^ w) :
    ∃ word : List Bool, word.length = w ∧
      Nat.ofDigits 2 (word.map fun bit => if bit then 1 else 0) = v := by
  let word := (Nat.digitsAppend 2 w v).map fun a => decide (a = 1)
  have hmap : word.map (fun bit => if bit then 1 else 0) = Nat.digitsAppend 2 w v := by
    simp only [word, List.map_map]
    calc
      _ = (Nat.digitsAppend 2 w v).map id := List.map_congr_left (by
        intro a ha
        have hb : a < 2 := Nat.lt_of_mem_digitsAppend (by decide) w a ha
        rcases (by omega : a = 0 ∨ a = 1) with h | h <;> subst a <;> rfl)
      _ = _ := List.map_id _
  refine ⟨word, ?_, ?_⟩
  · simpa only [word, List.length_map] using Nat.length_digitsAppend (by decide) w hv
  · rw [hmap]
    exact (Nat.setInvOn_digitsAppend_ofDigits (by decide) w).2 hv

lemma flatten_blocks_slice {α : Type} (blocks : List (List α)) (w : Nat)
    (hl : ∀ word ∈ blocks, word.length = w) (i : Nat) (hi : i < blocks.length) :
    (blocks.flatten.drop (i * w)).take w = blocks[i] := by
  induction blocks generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons word rest ih =>
    have hw := hl word List.mem_cons_self
    have hr : ∀ a ∈ rest, a.length = w := fun a ha => hl a (List.mem_cons_of_mem _ ha)
    cases i with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
      rw [← hw, List.take_left]
    | succ i =>
      have hi' : i < rest.length := by
        simp only [List.length_cons] at hi
        omega
      have hm : (i + 1) * w = w + i * w := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      have hd : (word ++ rest.flatten).drop w = rest.flatten := by
        rw [← hw, List.drop_left]
      simp only [List.flatten_cons, List.getElem_cons_succ, hm, ← List.drop_drop]
      rw [hd]
      exact ih hr i hi'

lemma flatten_blocks_length {α : Type} (blocks : List (List α)) (w : Nat)
    (hl : ∀ word ∈ blocks, word.length = w) :
    blocks.flatten.length = blocks.length * w := by
  induction blocks with
  | nil => simp
  | cons word rest ih =>
    have hw := hl word List.mem_cons_self
    have hr : ∀ a ∈ rest, a.length = w := fun a ha => hl a (List.mem_cons_of_mem _ ha)
    simp only [List.flatten_cons, List.length_append, List.length_cons, hw, ih hr]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

lemma encode_order (m w : Nat) (f : Fin m → Fin m) (hm : m ≤ 2 ^ w) :
    ∃ y : Array Bool, y.size = m * w ∧
      ∀ i : Fin m, Nat.ofDigits 2
        (((y.toList.drop (i.val * w)).take w).map fun bit => if bit then 1 else 0) =
          (f i).val := by
  classical
  have hb : ∀ i : Fin m, ∃ word : List Bool, word.length = w ∧
      Nat.ofDigits 2 (word.map fun bit => if bit then 1 else 0) = (f i).val :=
    fun i => binary_word w (f i).val (lt_of_lt_of_le (f i).isLt hm)
  choose word hl hd using hb
  let blocks := List.ofFn word
  have hblocks : ∀ a ∈ blocks, a.length = w := List.forall_mem_ofFn_iff.mpr hl
  refine ⟨blocks.flatten.toArray, ?_, ?_⟩
  · simp only [List.size_toArray, flatten_blocks_length blocks w hblocks,
      blocks, List.length_ofFn]
  · intro i
    rw [List.toList_toArray, flatten_blocks_slice blocks w hblocks i.val
      (by simp only [blocks, List.length_ofFn]; exact i.isLt)]
    simpa only [blocks, List.getElem_ofFn] using hd i

end Cslib.Algorithms.Lean.Graph
