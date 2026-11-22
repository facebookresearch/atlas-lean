/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.NoncrossingPartition.Small

/-!
# Consumer tests for the noncrossing-partition API

These examples exercise the public `NoncrossingPartition` API through its
narrow imports: instance resolution, the discrete/indiscrete extremal
partitions, block accessors, small-arity cardinalities, and the arity-three
classification.
-/

open Finset

namespace NoncrossingPartitionTest

/-- Instance resolution for the bundled type at a concrete arity. -/
example : Fintype (NoncrossingPartition 4) := inferInstance

example : DecidableEq (NoncrossingPartition 4) := inferInstance

example : PartialOrder (NoncrossingPartition 4) := inferInstance

example : OrderBot (NoncrossingPartition 3) := inferInstance

example : OrderTop (NoncrossingPartition 3) := inferInstance

/-- Crossing and noncrossing predicates are decidable on set partitions. -/
example (P : NoncrossingPartition.SetPartition 4) :
    Decidable (NoncrossingPartition.HasCrossing P) := inferInstance

example (P : NoncrossingPartition.SetPartition 4) :
    Decidable (NoncrossingPartition.IsNoncrossing P) := inferInstance

/-- Every set partition of `Fin 3` is noncrossing. -/
example (P : NoncrossingPartition.SetPartition 3) :
    NoncrossingPartition.IsNoncrossing P :=
  NoncrossingPartition.isNoncrossing_of_le_three (le_refl 3) P

/-- The bottom and top set partitions are noncrossing at every arity. -/
example : NoncrossingPartition.IsNoncrossing (⊥ : NoncrossingPartition.SetPartition 4) :=
  NoncrossingPartition.isNoncrossing_bot 4

example : NoncrossingPartition.IsNoncrossing (⊤ : NoncrossingPartition.SetPartition 4) :=
  NoncrossingPartition.isNoncrossing_top 4

/-- The order bottom and top are the discrete and indiscrete partitions. -/
example : (⊥ : NoncrossingPartition 2) = NoncrossingPartition.discrete 2 := rfl

example : (⊤ : NoncrossingPartition 2) = NoncrossingPartition.indiscrete 2 := rfl

example (P : NoncrossingPartition 3) : (⊥ : NoncrossingPartition 3) ≤ P := bot_le

example (P : NoncrossingPartition 3) : P ≤ (⊤ : NoncrossingPartition 3) := le_top

/-- Discrete and indiscrete partitions of `Fin 2` differ. -/
example : NoncrossingPartition.discrete 2 ≠ NoncrossingPartition.indiscrete 2 :=
  NoncrossingPartition.discrete_two_ne_indiscrete_two

/-- Blocks of the extremal partitions, and self-membership of blocks. -/
example (a : Fin 4) : NoncrossingPartition.block (NoncrossingPartition.discrete 4) a = {a} :=
  NoncrossingPartition.block_discrete 4 a

example (a : Fin 4) :
    NoncrossingPartition.block (NoncrossingPartition.indiscrete 4) a = Finset.univ :=
  NoncrossingPartition.block_indiscrete 4 a

example (P : NoncrossingPartition 4) (a : Fin 4) : a ∈ NoncrossingPartition.block P a :=
  NoncrossingPartition.mem_block_self P a

/-- Cardinalities at arities zero, one, and two. -/
example : Fintype.card (NoncrossingPartition 0) = 1 := NoncrossingPartition.card_zero

example : Fintype.card (NoncrossingPartition 1) = 1 := NoncrossingPartition.card_one

example : Fintype.card (NoncrossingPartition 2) = 2 := NoncrossingPartition.card_two

/-- The arity-two equivalence sends discrete to `0` and indiscrete to `1`. -/
example : NoncrossingPartition.twoEquiv (NoncrossingPartition.discrete 2) = 0 :=
  NoncrossingPartition.twoEquiv_apply_discrete

example : NoncrossingPartition.twoEquiv (NoncrossingPartition.indiscrete 2) = 1 :=
  NoncrossingPartition.twoEquiv_apply_indiscrete

/-- Every noncrossing partition of `Fin 1` is the indiscrete one. -/
example (P : NoncrossingPartition 1) : P = NoncrossingPartition.indiscrete 1 :=
  NoncrossingPartition.eq_indiscrete_one P

/-- Two-block partitions of `Fin 3` have exactly two blocks. -/
example (a : Fin 3) : (NoncrossingPartition.twoBlockPartition a).val.parts.card = 2 :=
  NoncrossingPartition.twoBlockPartition_parts_card a

/-- Arity-three classification: discrete, indiscrete, or a two-block partition. -/
example (P : NoncrossingPartition 3) :
    P = NoncrossingPartition.discrete 3 ∨ P = NoncrossingPartition.indiscrete 3 ∨
      ∃ a : Fin 3, P = NoncrossingPartition.twoBlockPartition a :=
  NoncrossingPartition.eq_discrete_or_indiscrete_or_twoBlock_three P

end NoncrossingPartitionTest
