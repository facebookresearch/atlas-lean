/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopLowTempCorrelation
import Code.Onsager.SignedLoopGeometricDualWeighted





open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section



def kwg_pathEdgeIndex (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) : {edge // edge ∈ path.edges} -> kwg_Edge P :=
  fun edge => ⟨edge.1, path.edges_subset_edgeSet edge.2⟩


def kwg_pathEdgeIndices (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) : List (kwg_Edge P) :=
  path.edges.attach.map (kwg_pathEdgeIndex P path)

@[simp] theorem kwg_pathEdgeIndices_map_val
    (P : PlanarZ2Subgraph) {u v : P.V} (path : P.G.Walk u v) :
    (kwg_pathEdgeIndices P path).map Subtype.val = path.edges := by
  simp [kwg_pathEdgeIndices, kwg_pathEdgeIndex]



def kwg_pathDefectCount (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (F : Finset (kwg_Edge P)) : Nat :=
  (kwg_pathEdgeIndices P path).countP fun edge => decide (edge ∈ F)


def kwg_pathDefectSign (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (F : Finset (kwg_Edge P)) : Real :=
  if Even (kwg_pathDefectCount P path F) then 1 else -1



theorem kwg_pathDefectCount_cutSet (P : PlanarZ2Subgraph)
    (config : ConfigSpace P.V) {u v : P.V} (path : P.G.Walk u v) :
    kwg_pathDefectCount P path
        (kwg_cutSet (kwg_primalEnds P) config) =
      kwd_crossCount (kwd_sideBoundary config) path := by
  unfold kwg_pathDefectCount kwg_pathEdgeIndices kwd_crossCount
  rw [List.countP_map]
  calc
    _ = path.edges.attach.countP
        (kwd_sideBoundary config ∘ Subtype.val) := by
      apply List.countP_congr
      intro edge _
      simp only [Function.comp_apply, kwg_pathEdgeIndex,
        decide_eq_true_eq]
      rw [kwg_mem_cutSet]
      rcases edge with ⟨edge, hedge⟩
      induction edge using Sym2.ind with
      | _ x y =>
          have hadj := path.adj_of_mem_edges hedge
          rw [kwg_primalEnds, kwg_isSplit_mk, kwd_sideBoundary_mk]
          cases config x <;> cases config y <;> decide
    _ = (path.edges.attach.map Subtype.val).countP
        (kwd_sideBoundary config) := by rw [List.countP_map]
    _ = _ := by simp



theorem kwg_pathDefectSign_cutSet (P : PlanarZ2Subgraph)
    (config : ConfigSpace P.V) {u v : P.V} (path : P.G.Walk u v) :
    kwg_pathDefectSign P path
        (kwg_cutSet (kwg_primalEnds P) config) =
      ons_lowTempPathSign P.G config path := by
  unfold kwg_pathDefectSign ons_lowTempPathSign
  rw [kwg_pathDefectCount_cutSet]



def kwg_lowTempPathDualSum (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) : Real :=
  ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then
      kwg_pathDefectSign P path F * Real.exp (-2 * beta) ^ F.card
    else 0


def kwg_lowTempDualSum (P : PlanarZ2Subgraph) (beta : Real) : Real :=
  ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then
      Real.exp (-2 * beta) ^ F.card
    else 0

theorem ons_lowTempPathNumerator_eq_kwg_dual
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    ons_lowTempPathNumerator P.G beta path =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        kwg_lowTempPathDualSum P beta path := by
  let observable : Finset (kwg_Edge P) -> Real := fun F =>
    kwg_pathDefectSign P path F * Real.exp (-2 * beta) ^ F.card
  calc
    ons_lowTempPathNumerator P.G beta path =
        ∑ config : ConfigSpace P.V,
          observable (kwg_cutSet (kwg_primalEnds P) config) := by
      unfold ons_lowTempPathNumerator observable
      apply Finset.sum_congr rfl
      intro config _
      rw [kwg_pathDefectSign_cutSet, kwg_primalCut_card]
    _ = (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        ∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 :=
      kwg_weightedCutEvenSum P observable
    _ = _ := by rfl

theorem ons_lowTempContourDenominator_eq_kwg_dual
    (P : PlanarZ2Subgraph) (beta : Real) :
    ons_lowTempContourDenominator P.G beta =
      (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        kwg_lowTempDualSum P beta := by
  let observable : Finset (kwg_Edge P) -> Real := fun F =>
    Real.exp (-2 * beta) ^ F.card
  calc
    ons_lowTempContourDenominator P.G beta =
        ∑ config : ConfigSpace P.V,
          observable (kwg_cutSet (kwg_primalEnds P) config) := by
      unfold ons_lowTempContourDenominator observable
      apply Finset.sum_congr rfl
      intro config _
      rw [kwg_primalCut_card]
    _ = (2 : Real) ^ Nat.card P.G.ConnectedComponent *
        ∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 :=
      kwg_weightedCutEvenSum P observable
    _ = _ := by rfl


theorem isingExpectation_twoPoint_eq_kwg_lowTempDualRatio
    (P : PlanarZ2Subgraph) (beta : Real)
    {u v : P.V} (path : P.G.Walk u v) :
    isingExpectation P.G beta 0
        (fun config => spin config u * spin config v) =
      kwg_lowTempPathDualSum P beta path /
        kwg_lowTempDualSum P beta := by
  rw [isingExpectation_twoPoint_eq_lowTempPathRatio,
    ons_lowTempPathNumerator_eq_kwg_dual,
    ons_lowTempContourDenominator_eq_kwg_dual]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (2 : Real) ≠ 0))

end

end StatMech.Onsager
