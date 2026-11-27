/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
