/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.LocallySparseTripleSystem

/-! # Tests for Erdős Problem 1076 as worded -/

namespace MathlibExtTest.LocallySparseTripleSystem

open Finset
open MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted

-- With fewer than five vertices no five vertices exist, so all four triples on four vertices
-- are allowed.
example : exSingle 5 4 = 4 := by
  unfold exSingle
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨univ.powersetCard 3, fun e he => (mem_powersetCard.mp he).2, ?_, by decide⟩
    rintro ⟨S, hS, -⟩
    have := card_le_univ S
    simp only [Fintype.card_fin] at this
    omega
  · rintro _ ⟨E, h3, -, rfl⟩
    calc E.card ≤ (univ.powersetCard 3 : Finset (Finset (Fin 4))).card :=
          card_le_card fun e he => mem_powersetCard.mpr ⟨subset_univ e, h3 e he⟩
      _ = 4 := by decide

-- On exactly five vertices the only five-vertex set is everything, so at most two triples fit,
-- and two triples sharing a pair attain this.
example : exSingle 5 5 = 2 := by
  unfold exSingle
  apply IsGreatest.csSup_eq
  constructor
  · let E : Finset (Finset (Fin 5)) := {{0, 1, 2}, {0, 1, 3}}
    refine ⟨E, by rw [SetFamily.isUniform_iff]; decide, ?_, by decide⟩
    rintro ⟨S, -, hS⟩
    have := (card_filter_le E fun e => e ⊆ S).trans (by decide : E.card ≤ 2)
    omega
  · rintro _ ⟨E, -, hfree, rfl⟩
    by_contra! h
    exact hfree ⟨univ, by simp, by rw [filter_true_of_mem fun e _ => subset_univ e]; omega⟩

-- For `k = 2` every two vertices span `k - 2 = 0` triples, so no hypergraph qualifies and the
-- supremum of the empty set is `0`.
example : exSingle 2 3 = 0 := by
  have hempty : {m | ∃ E : Finset (Finset (Fin 3)), SetFamily.IsUniform E 3 ∧
      ¬ SetFamily.ContainsSubgraph E 2 (2 - 2) ∧ E.card = m} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro m ⟨E, -, hE, -⟩
    exact hE ⟨{0, 1}, by decide, Nat.zero_le _⟩
  rw [exSingle, hempty, csSup_empty, Nat.bot_eq_zero]

example : ¬ singleFamilyAsymptotic :=
  singleFamilyAsymptotic_refuted

end MathlibExtTest.LocallySparseTripleSystem
