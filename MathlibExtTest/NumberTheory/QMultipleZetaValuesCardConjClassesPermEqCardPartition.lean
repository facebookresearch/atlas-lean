/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QMultipleZetaValuesCardConjClassesPermEqCardPartition

/-!
# Tests for the number of conjugacy classes of the symmetric group

The cases `n = 0` and `n = 1` have one conjugacy class, and the number of classes
is positive for every `n`.

Reference: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (arXiv:2111.00051).
-/

namespace MathlibExtTest.NumberTheory.QMultipleZetaValuesCardConjClassesPermEqCardPartition

example : Nat.card (ConjClasses (Equiv.Perm (Fin 0))) = 1 := by
  simpa using MetaMathlibExt.card_conjClasses_perm_eq_card_partition 0

example : Nat.card (ConjClasses (Equiv.Perm (Fin 1))) = 1 := by
  simpa using MetaMathlibExt.card_conjClasses_perm_eq_card_partition 1

example (n : ℕ) : 0 < Nat.card (ConjClasses (Equiv.Perm (Fin n))) := by
  rw [MetaMathlibExt.card_conjClasses_perm_eq_card_partition]
  exact Fintype.card_pos

end MathlibExtTest.NumberTheory.QMultipleZetaValuesCardConjClassesPermEqCardPartition
