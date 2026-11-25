/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Sum
import MathlibExt.Combinatorics.ArithmeticalStructureCoconutSubdivision

namespace MetaMathlibExt.CoconutSubdivisionTest

private def edgeLabels : (Fin 1 ⊕ Fin 1 → ℕ) × (Fin 1 ⊕ Fin 1 → ℕ) :=
  (fun _ => 1, fun _ => 1)

private theorem edge_structure :
    IsArithmeticalStructure (coconutTree 1 1) edgeLabels.1 edgeLabels.2 := by
  refine ⟨fun _ => one_pos, fun _ => one_pos, ?_, fun _ h => Nat.dvd_one.mp (h (.inl 0))⟩
  rintro (j | l)
  · have h : {w | (coconutTree 1 1).Adj (.inl j) w} = {Sum.inr 0} := by
      ext (k | k)
      · simp [coconutTree_adj_inl_inl]
      · simp [coconutTree_adj_inl_inr, Subsingleton.elim k 0]
    rw [h, finsum_mem_singleton]
    rfl
  · have h : {w | (coconutTree 1 1).Adj (.inr l) w} = {Sum.inl 0} := by
      ext (k | k)
      · rw [Set.mem_ofPred_eq, SimpleGraph.adj_comm, coconutTree_adj_inl_inr]
        simp [Subsingleton.elim k 0]
      · simp [coconutTree_not_adj_inr_inr]
    rw [h, finsum_mem_singleton]
    rfl

-- Insertion at the first path vertex retains the central vertex's leaf neighbour.
private theorem first_labels : coconutSubdivide 0 edgeLabels =
    (Sum.elim ![1, 2] ![1], Sum.elim ![1, 1] ![1]) := by
  decide

example :
    IsArithmeticalStructure (coconutTree 2 1) (Sum.elim ![1, 2] ![1]) (Sum.elim ![1, 1] ![1]) := by
  simpa only [first_labels] using edge_structure.coconutSubdivide 0

-- With a predecessor and no leaves, both adjacent d-labels increase.
example : coconutSubdivide (p := 2) (s := 0) 1 (fun _ => 1, fun _ => 1) =
    (Sum.elim ![2, 1, 2] ![], Sum.elim ![1, 2, 1] ![]) := by
  decide

end MetaMathlibExt.CoconutSubdivisionTest
