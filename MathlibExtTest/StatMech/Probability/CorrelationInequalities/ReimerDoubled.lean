/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDoubled

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerDoubled`

* `dbl` computed (`dbl {0} {1} = {inl 0, inr 1}`) and its membership lemmas;
* `card_boxDoubled` for `famA = {∅, {0}}`, `famB = {∅, {1}}` (`#boxDoubled = 4`), and
  `card_boxFamily_le_boxDoubled`;
* `doubleCompress_eq_self` for the empty family (both closure hypotheses proved).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerDoubled

open _root_.StatMech
open scoped FinsetFamily

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

-- `dbl {0} {1}` records `0` on the left and `1` on the right.
example : Sum.inl 0 ∈ dbl ({0} : Finset (Fin 2)) {1} ∧ Sum.inr 1 ∈ dbl ({0} : Finset (Fin 2)) {1} ∧
    Sum.inr 0 ∉ dbl ({0} : Finset (Fin 2)) {1} := by
  simp

-- `#boxDoubled famA famB = 4`, the number of disjoint pairs.
example : (boxDoubled famA famB).card = 4 := by
  rw [card_boxDoubled]
  decide

-- `#(famA ○ famB) ≤ #boxDoubled famA famB`.
example : (famA ○ famB).card ≤ (boxDoubled famA famB).card :=
  card_boxFamily_le_boxDoubled _ _

-- The empty family is fixed by `doubleCompress`.
example : doubleCompress (0 : Fin 2) ∅ = ∅ :=
  doubleCompress_eq_self 0 (fun _ h => absurd h (Finset.notMem_empty _))
    (fun _ h => absurd h (Finset.notMem_empty _))

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerDoubled
