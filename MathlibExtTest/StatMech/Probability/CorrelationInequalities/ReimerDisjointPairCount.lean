/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDisjointPairCount

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyStep`

On `Fin 2` with the families `famA = {∅, {0}}`, `famB = {∅, {1}}`: `dpairsCount` is computed
(`4`, all pairs disjoint) and on `famA, famA` (`3`); `dpairsCount_le_mul` and the cardinality part
of `reimer_butterfly_compress_step` are applied.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyStep

open _root_.StatMech

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

-- All four pairs of `famA × famB` are disjoint.
example : dpairsCount famA famB = 4 := by decide

-- In `famA × famA` the pair `({0}, {0})` is not disjoint.
example : dpairsCount famA famA = 3 := by decide

-- `dpairsCount_le_mul` at `famA, famA`: `3 ≤ 4`.
example : dpairsCount famA famA ≤ famA.card * famA.card := dpairsCount_le_mul _ _

-- One compression step preserves the size of the doubled family.
example : (doubleCompress 0 (boxDoubled famA famB)).card = (boxDoubled famA famB).card :=
  (reimer_butterfly_compress_step famA famB 0).1

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyStep
