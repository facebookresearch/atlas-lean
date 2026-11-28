/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.SetTheory.Cardinal.Finite
import MathlibExt.Combinatorics.Enumerative.DescendingNaplesPaddedDyckWord

/-! # Tests for the padded Dyck word count -/

open MetaMathlibExt DyckStep

open Classical in
-- One car still gives exactly one word when the padding is longer than the original walk.
example : (Finset.univ.filter fun p : {p : DyckWord // p.semilength = 1 + 3} =>
    List.replicate 3 U <+: p.1.toList ∧ List.replicate (3 + 1) D <:+ p.1.toList).card = 1 := by
  rw [← descendingNaplesCount_eq_card_dyckPath (by decide) (by decide)]
  decide

open Classical in
-- The count for three cars and one backward step is nine, by direct parking enumeration.
example : (Finset.univ.filter fun p : {p : DyckWord // p.semilength = 3 + 1} =>
    List.replicate 1 U <+: p.1.toList ∧ List.replicate (1 + 1) D <:+ p.1.toList).card = 9 := by
  rw [← descendingNaplesCount_eq_card_dyckPath (by decide) (by decide)]
  decide

-- Padding DUUD with one step at each end gives UDUUDD, with exactly two final Down steps.
example : let w := (0 : DyckWord).nest + (0 : DyckWord).nest.nest
    [U] <+: w.toList ∧ [D, D] <:+ w.toList ∧ ¬ [D, D, D] <:+ w.toList := by
  decide

-- UDUUDD has an Up step after exactly one Down step.
example : let w := (0 : DyckWord).nest + (0 : DyckWord).nest.nest
    ∃ a t, w.toList = a ++ U :: t ∧ a.count D = 1 := by
  exact ⟨[U, D], [U, D, D], by decide, by decide⟩

-- In UUUDDD, every Up step precedes every Down step.
example : ¬ ∃ a t, (0 : DyckWord).nest.nest.nest.toList = a ++ U :: t ∧ a.count D = 1 := by
  let l := [U, U, U, D, D, D]
  change ¬ ∃ a t, l = a ++ U :: t ∧ a.count D = 1
  rintro ⟨a, t, he, hd⟩
  have hi : a.length < l.length := by simp [he]
  have hstep : l[a.length]? = some U := by
    rw [he, List.getElem?_append_right le_rfl]
    simp
  have hcount : (l.take a.length).count D = 1 := by rw [he, List.take_left, hd]
  have hbad : ∀ i : Fin 6, let s := [U, U, U, D, D, D]
      s[i.val]? = some U → (s.take i.val).count D ≠ 1 := by decide +kernel
  exact hbad ⟨a.length, hi⟩ hstep hcount

-- Transfer the independently computed preference count to the marked Dyck words.
example : Nat.card {w : {w : DyckWord // w.semilength = 3} //
    ∃ a t, w.1.toList = a ++ U :: t ∧ a.count D = (1 : Fin 3).val} = 3 := by
  rw [← Nat.card_congr (decreasingParkingPreferenceEquivDyckWord (1 : Fin 3)),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

-- The height uses only the requested prefix, or the entire word if the index is larger.
example : dyckStepHeight [U, D, D] 3 = -1 ∧ dyckStepHeight [U, U, D] 2 = 2 ∧
    dyckStepHeight [U, U, D] 5 = 1 := by
  decide +kernel

-- Check append and Up-step simplification at symbolic indices, including after simplifying length.
example (l r : List DyckStep) (j : ℕ) :
    dyckStepHeight (l ++ r) j = dyckStepHeight l j + dyckStepHeight r (j - l.length) := by
  simp

example (l r : List DyckStep) :
    dyckStepHeight (l ++ r) (l ++ r).length =
      dyckStepHeight l (l.length + r.length) + dyckStepHeight r r.length := by
  simp

example (l : List DyckStep) (j : ℕ) :
    dyckStepHeight (U :: l) (j + 1) = dyckStepHeight l j + 1 := by
  simp
