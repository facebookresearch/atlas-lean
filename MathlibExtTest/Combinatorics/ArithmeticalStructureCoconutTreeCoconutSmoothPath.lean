/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath

/-!
# Tests for path smoothing on coconut trees

Smoothing the arithmetical structure with `d = (1, 2)` and `r = (1, 1)` on the path
of `CT(2, 1)` at its first path vertex gives the all-ones structure on `CT(1, 1)`.
-/

open MetaMathlibExt

namespace MathlibExtTest.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath

private def pathLabels : (Fin 2 ⊕ Fin 1 → ℕ) × (Fin 2 ⊕ Fin 1 → ℕ) :=
  (Sum.elim ![1, 2] ![1], Sum.elim ![1, 1] ![1])

private theorem path_structure :
    IsArithmeticalStructure (coconutTree 2 1) pathLabels.1 pathLabels.2 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rintro (j | l)
    · fin_cases j
      · simp only [Fin.mk_zero]
        have h : {w | (coconutTree 2 1).Adj (.inl 0) w} = {Sum.inl 1} := by
          ext (k | k)
          · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff,
              coconutTree_adj_inl_inl, Sum.inl.injEq, Fin.ext_iff,
              Fin.val_zero, Fin.val_one]
            have hk := k.isLt
            omega
          · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff,
              coconutTree_adj_inl_inr, Fin.val_zero]
            rw [Subsingleton.elim k 0]
            decide
        rw [h, finsum_mem_singleton]
        rfl
      · simp only [Fin.mk_one]
        have h : {w | (coconutTree 2 1).Adj (.inl 1) w} =
            {Sum.inl 0, Sum.inr 0} := by
          ext (k | k)
          · simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
              coconutTree_adj_inl_inl, Sum.inl.injEq, Fin.ext_iff,
              Fin.val_zero, Fin.val_one, Sum.inl_ne_inr, or_false]
            have hk := k.isLt
            omega
          · simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
              coconutTree_adj_inl_inr, Fin.val_one]
            rw [Subsingleton.elim k 0]
            decide
        rw [h, finsum_mem_insert _ (by simp) (Set.toFinite _), finsum_mem_singleton]
        rfl
    · fin_cases l
      simp only [Fin.mk_zero]
      have h : {w | (coconutTree 2 1).Adj (.inr 0) w} = {Sum.inl 1} := by
        ext (k | k)
        · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Sum.inl.injEq,
            Fin.ext_iff, Fin.val_one]
          rw [SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
          have hk := k.isLt
          omega
        · have hneg : ¬(coconutTree 2 1).Adj (.inr 0) (.inr k) :=
            coconutTree_not_adj_inr_inr _ _
          simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
          rw [iff_false_intro hneg]
          simp [Subsingleton.elim k 0]
      rw [h, finsum_mem_singleton]
      rfl
  · intro g hg
    have h1 : pathLabels.2 (.inl 0) = 1 := rfl
    have hdiv := hg (.inl 0)
    rw [h1] at hdiv
    exact Nat.dvd_one.mp hdiv

-- Smoothing at the first path vertex gives the all-ones labelings on `CT(1, 1)`.
private theorem smooth_labels : coconutSmoothPath 0 pathLabels =
    (Sum.elim ![1] ![1], Sum.elim ![1] ![1]) := by
  decide

-- The smoothed labelings form an arithmetical structure on `CT(1, 1)`.
example : IsArithmeticalStructure (coconutTree 1 1)
    (Sum.elim ![1] ![1]) (Sum.elim ![1] ![1]) := by
  have h := path_structure.coconutSmoothPath (by decide) 0 (by decide) (by decide)
  simpa only [smooth_labels] using h

end MathlibExtTest.Combinatorics.ArithmeticalStructureCoconutTreeCoconutSmoothPath
