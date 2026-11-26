/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80
import Mathlib.Data.ZMod.Basic

/-!
# Tests for defect-zero characters and commutator counts

The refutation gives a counterexample with a prime dividing the group order.
The cyclic group of order two tests both a nonempty and an empty commutator fiber.
-/

open MathlibExt.GroupTheory.DefectZeroBlocksCommutatorCountKourovka12Problem80Wanted

example : ∃ (p : ℕ) (_ : p.Prime) (G : Type) (_ : Group G) (_ : Finite G),
    IsSimpleGroup G ∧ p ∣ Nat.card G ∧
    Nat.card (defectZeroCharacters p G) ≠ Nat.card (nondivisibleCommutatorClasses p G) := by
  by_contra! h
  exact simpleDefectZeroBlocksEqNondivisibleClasses_refuted
    (fun p hp G grp fin => h p hp G grp fin)

private abbrev C₂ := Multiplicative (ZMod 2)

example : commutatorSolutionCount (1 : C₂) = 4 := by
  rw [commutatorSolutionCount, Nat.card_eq_fintype_card]
  decide

example : commutatorSolutionCount (Multiplicative.ofAdd (1 : ZMod 2)) = 0 := by
  rw [commutatorSolutionCount, Nat.card_eq_fintype_card]
  decide
