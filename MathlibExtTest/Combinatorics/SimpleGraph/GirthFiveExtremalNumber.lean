/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalNumber

open Finset SimpleGraph
open MathlibExt.Combinatorics.SimpleGraph.GirthFiveExtremalValuesWanted

-- The empty vertex type gives the zero boundary value of the finite supremum.
example : girthFiveExtremalNumber 0 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold girthFiveExtremalNumber
  exact Finset.sup_le fun G _ => by simpa using G.card_edgeFinset_le_card_choose_two

-- On two vertices the acyclic one-edge path qualifies via its infinite extended girth.
example : girthFiveExtremalNumber 2 = 1 := by
  classical
  unfold girthFiveExtremalNumber
  apply le_antisymm
  · exact Finset.sup_le fun G _ => by simpa using G.card_edgeFinset_le_card_choose_two
  · refine le_trans ?_ (Finset.le_sup (b := pathGraph 2) ?_)
    · have hcard : #(pathGraph 2).edgeFinset + 1 = 2 := by
        simpa only [Fintype.card_fin] using (isTree_pathGraph_add_one 1).card_edgeFinset
      have hone : 1 ≤ #(pathGraph 2).edgeFinset := by omega
      convert hone
    · simp only [mem_filter, mem_univ, true_and, (isAcyclic_pathGraph 2).egirth_eq_top, le_top]
