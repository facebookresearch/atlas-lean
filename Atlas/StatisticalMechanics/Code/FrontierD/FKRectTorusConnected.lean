/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusEdgeFinset
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant

open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

private theorem fkRect_cyclicPred_eq_sub_one {N : Nat} (hN : 1 < N)
    (i : Fin N) :
    SixVertexArrows.cyclicPred (by omega) i = i - ⟨1, hN⟩ := by
  letI : NeZero N := ⟨by omega⟩
  apply Fin.ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_mk, Fin.sub_def]
  congr 1
  omega

private theorem fkRect_cycleGraph_adj_pred_or {N : Nat} (hN : 2 < N)
    {i j : Fin N} (hij : (cycleGraph N).Adj i j) :
    j = SixVertexArrows.cyclicPred (by omega) i ∨
      i = SixVertexArrows.cyclicPred (by omega) j := by
  letI : NeZero N := ⟨by omega⟩
  rw [cycleGraph_adj'] at hij
  let one : Fin N := ⟨1, by omega⟩
  have hone : one.val = 1 := rfl
  rcases hij with hij | hij
  · have hsub : i - j = one := by
      apply Fin.ext
      exact hij.trans hone.symm
    left
    rw [fkRect_cyclicPred_eq_sub_one]
    change j = i - one
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub).symm
  · have hsub : j - i = one := by
      apply Fin.ext
      exact hij.trans hone.symm
    right
    rw [fkRect_cyclicPred_eq_sub_one]
    change i = j - one
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using (sub_eq_iff_eq_add.mp hsub).symm



theorem fkRectTorusGraph_adj_verticalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectTorusGraph R).Adj (x, y)
      (x, SixVertexArrows.cyclicPred R.height_pos y) := by
  exact ⟨(true, (x, y)), rfl⟩



theorem fkRectTorusGraph_reachable_horizontalPred (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (fkRectTorusGraph R).Reachable (x, y)
      (SixVertexArrows.cyclicPred R.width_pos x, y) := by
  let xp := SixVertexArrows.cyclicPred R.width_pos x
  let yp := SixVertexArrows.cyclicPred R.height_pos y
  by_cases hy : Even y.val
  · have hdiag : (fkRectTorusGraph R).Adj (x, y) (xp, yp) := by
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    have hvert : (fkRectTorusGraph R).Adj (xp, y) (xp, yp) :=
      fkRectTorusGraph_adj_verticalPred R xp y
    exact hdiag.reachable.trans hvert.symm.reachable
  · have hvert : (fkRectTorusGraph R).Adj (x, y) (x, yp) :=
      fkRectTorusGraph_adj_verticalPred R x y
    have hdiag : (fkRectTorusGraph R).Adj (xp, y) (x, yp) := by
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    exact hvert.reachable.trans hdiag.symm.reachable



def fkRectCoordinateCycleGraph (R : FKRectTorus) :
    SimpleGraph R.Vertex :=
  cycleGraph R.width □ cycleGraph R.height

theorem fkRectCoordinateCycleGraph_connected (R : FKRectTorus) :
    (fkRectCoordinateCycleGraph R).Connected := by
  let _ : Nonempty (Fin R.width) := Fin.pos_iff_nonempty.mp R.width_pos
  let _ : Nonempty (Fin R.height) := Fin.pos_iff_nonempty.mp R.height_pos
  unfold fkRectCoordinateCycleGraph
  exact ⟨cycleGraph_preconnected.boxProd cycleGraph_preconnected⟩


theorem fkRectTorusGraph_reachable_of_coordinate_adj (R : FKRectTorus)
    {u v : R.Vertex} (huv : (fkRectCoordinateCycleGraph R).Adj u v) :
    (fkRectTorusGraph R).Reachable u v := by
  rcases u with ⟨ux, uy⟩
  rcases v with ⟨vx, vy⟩
  change ((cycleGraph R.width).Adj ux vx ∧ uy = vy) ∨
    ((cycleGraph R.height).Adj uy vy ∧ ux = vx) at huv
  rcases huv with (⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩)
  · subst vy
    rcases fkRect_cycleGraph_adj_pred_or R.width_gt_two hfst with h | h
    · subst vx
      exact fkRectTorusGraph_reachable_horizontalPred R ux uy
    · subst ux
      exact (fkRectTorusGraph_reachable_horizontalPred R vx uy).symm
  · subst vx
    rcases fkRect_cycleGraph_adj_pred_or R.height_gt_two
      (i := uy) (j := vy) hfst with h | h
    · rw [h]
      exact (fkRectTorusGraph_adj_verticalPred R ux uy).reachable
    · rw [h]
      exact (fkRectTorusGraph_adj_verticalPred R ux vy).symm.reachable


theorem fkRectTorusGraph_connected (R : FKRectTorus) :
    (fkRectTorusGraph R).Connected := by
  let _ : Nonempty R.Vertex :=
    ⟨(⟨0, R.width_pos⟩, ⟨0, R.height_pos⟩)⟩
  refine ⟨?_⟩
  intro u v
  have huv := (fkRectCoordinateCycleGraph_connected R).preconnected u v
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  induction huv with
  | refl => rfl
  | tail hxy hyz ih =>
      have hstep := fkRectTorusGraph_reachable_of_coordinate_adj R hyz
      rw [SimpleGraph.reachable_iff_reflTransGen] at hstep
      exact ih.trans hstep

theorem fkRectFinsetClusterCount_univ (R : FKRectTorus) :
    fkRectFinsetClusterCount R Finset.univ = 1 := by
  unfold fkRectFinsetClusterCount fkRectNumClusters
  have hconn :
      (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R Finset.univ)).Connected := by
    rw [fkRectOpenGraph_configurationOfEdges_univ]
    exact fkRectTorusGraph_connected R
  have hcard := card_components_eq_one_of_connected hconn
  simpa only [Nat.card_eq_fintype_card] using hcard

end StatMech.FrontierD
