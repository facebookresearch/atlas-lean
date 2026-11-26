/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.Perm.ConjClassesPartition

/-! # Tests for the partition of a permutation's conjugacy class -/

open MetaMathlibExt

-- The class of the empty permutation maps to the empty partition.
example :
    ∃ e : ConjClasses (Equiv.Perm (Fin 0)) ≃ (Fintype.card (Fin 0)).Partition,
      (e (ConjClasses.mk 1)).parts = 0 := by
  obtain ⟨e, he⟩ := exists_conjClasses_perm_equiv_partition 0
  refine ⟨e, ?_⟩
  rw [he]
  simp [Equiv.Perm.parts_partition]

-- Two disjoint transpositions contribute two parts of size two, and the fixed point contributes one.
example :
    ∃ e : ConjClasses (Equiv.Perm (Fin 5)) ≃ (Fintype.card (Fin 5)).Partition,
      (e (ConjClasses.mk (Equiv.swap 0 1 * Equiv.swap 2 3))).parts = {2, 2, 1} := by
  obtain ⟨e, he⟩ := exists_conjClasses_perm_equiv_partition 5
  refine ⟨e, ?_⟩
  have hcycle := Equiv.Perm.cycleType_swap_mul_swap_of_nodup
    (show ([0, 1, 2, 3] : List (Fin 5)).Nodup by decide)
  rw [he, Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hcycle]
  decide
