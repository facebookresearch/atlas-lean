/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.SetTheory.Cardinal.Finite
import MathlibExt.GroupTheory.Perm.ConjClassesPartition

/-!
# Conjugacy classes of the symmetric group

The number of conjugacy classes of permutations of `Fin n` equals the number of
partitions of `n`: it is the cardinality form of `exists_conjClasses_perm_equiv_partition`,
the correspondence by cycle type, fixed points counting as cycles of length one.

Reference: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (arXiv:2111.00051).
-/

namespace MetaMathlibExt

/-- **Number of conjugacy classes of the symmetric group.** For every natural number $n$, the
number of conjugacy classes of the symmetric group $S_n$ equals the number $p(n)$ of partitions
of $n$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem card_conjClasses_perm_eq_card_partition (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card n.Partition := by
  obtain ⟨e, -⟩ := exists_conjClasses_perm_equiv_partition n
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end MetaMathlibExt
