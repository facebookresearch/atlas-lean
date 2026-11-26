/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.StrongMason
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Combinatorics.Matroid.StrongMason` -/

namespace MathlibExtTest.Combinatorics.Matroid.StrongMason

open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

-- Test section: `independentSetCount`.

/-- In the free matroid on `Fin 4` every finset is independent, so `independentSetCount` gives the
binomial coefficients. -/
private lemma independentSetCount_freeOn (k : ℕ) :
    independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) k = Nat.choose 4 k := by
  have hset : {I ∈ Set.powersetCard (Fin 4) k |
      (Matroid.freeOn Set.univ).Indep (I : Set (Fin 4))} =
        ↑(Finset.powersetCard k (Finset.univ : Finset (Fin 4))) := by
    ext I
    simp
  rw [independentSetCount, hset, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

-- The loopy matroid on `Fin 3`: the empty set is its only independent set.
example : independentSetCount (Matroid.loopyOn (Set.univ : Set (Fin 3))) 0 = 1 := by
  have hset : {I ∈ Set.powersetCard (Fin 3) 0 |
      (Matroid.loopyOn Set.univ).Indep (I : Set (Fin 3))} = {∅} := by
    ext I
    simp
  rw [independentSetCount, hset, Set.ncard_singleton]

example : independentSetCount (Matroid.loopyOn (Set.univ : Set (Fin 3))) 1 = 0 := by
  have hset : {I ∈ Set.powersetCard (Fin 3) 1 |
      (Matroid.loopyOn Set.univ).Indep (I : Set (Fin 3))} = ∅ := by
    ext I
    simp only [Set.mem_ofPred_eq, Set.powersetCard.mem_iff, Matroid.loopyOn_indep_iff,
      Finset.coe_eq_empty, Set.mem_empty_iff_false, iff_false, not_and]
    rintro h rfl
    simp at h
  rw [independentSetCount, hset, Set.ncard_empty]

example : independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 2 = 6 := by
  rw [independentSetCount_freeOn]
  decide

-- Test section: `strong_mason_conjecture`.

-- The case `k = 1` for an arbitrary finite matroid with at least two elements.
example {α : Type*} (M : _root_.Matroid α) [M.Finite] (h : 1 < M.E.ncard) :
    independentSetCount M 0 * independentSetCount M 2 * 2 * M.E.ncard ≤
      independentSetCount M 1 ^ 2 * (M.E.ncard - 1) := by
  have key := strong_mason_conjecture M 1 one_pos h
  have hn : M.E.ncard - 1 + 1 = M.E.ncard := by omega
  simpa [hn] using key

-- The free matroid on four elements at `k = 2`: here `I_k = C(4, k)` and the inequality
-- `4 * 4 * 3 * 3 ≤ 6 ^ 2 * 2 * 2` is an equality.
example : independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 1 *
      independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 3 * 3 * 3 ≤
    independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 2 ^ 2 * 2 * 2 := by
  have hn : (Matroid.freeOn (Set.univ : Set (Fin 4))).E.ncard = 4 := by simp
  have key := strong_mason_conjecture (Matroid.freeOn (Set.univ : Set (Fin 4))) 2 two_pos
    (by rw [hn]; norm_num)
  rw [hn] at key
  simpa using key

example : independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 1 *
      independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 3 * 3 * 3 =
    independentSetCount (Matroid.freeOn (Set.univ : Set (Fin 4))) 2 ^ 2 * 2 * 2 := by
  simp only [independentSetCount_freeOn]
  decide

end MathlibExtTest.Combinatorics.Matroid.StrongMason
