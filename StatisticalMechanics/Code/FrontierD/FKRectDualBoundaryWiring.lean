/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalAdaptiveProjection
import Mathlib.Combinatorics.SimpleGraph.Hasse









open SimpleGraph

namespace StatMech.FrontierD

noncomputable section

theorem finitePeriodicSucc_fkRectRightColumn
    (R : FKRectTorus) :
    finitePeriodicSucc R.width_pos (fkRectRightColumn R) =
      fkRectLeftColumn R := by
  apply Fin.ext
  change (R.width - 1 + 1) % R.width = 0
  rw [Nat.sub_add_cancel
    ((Nat.one_le_iff_ne_zero).2 (Nat.ne_of_gt R.width_pos)), Nat.mod_self]

theorem fkRect_cyclicPred_eq_of_val_succ
    {N : Nat} (hN : 0 < N) {u v : Fin N}
    (huv : u.val + 1 = v.val) :
    SixVertexArrows.cyclicPred hN v = u := by
  apply Fin.ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_mk]
  have hvpos : 1 ≤ v.val := by omega
  have hsum : v.val + N - 1 = (v.val - 1) + N := by omega
  rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt]
  · omega
  · omega



theorem fkRectDualOpenGraph_adj_right_of_val_succ
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectCutClosedConfiguration R eta)
    {u v : Fin R.height} (huv : u.val + 1 = v.val) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta)).Adj
      (fkRectRightColumn R, u) (fkRectRightColumn R, v) := by
  let e : R.EdgeIndex := (true, (fkRectRightColumn R, v))
  have hecross : fkRectDualEdgeToEdge R e =
      (false, (fkRectLeftColumn R, v)) := by
    simp only [e, fkRectDualEdgeToEdge, ↓reduceIte]
    rw [finitePeriodicSucc_fkRectRightColumn]
  have hecut : (false, (fkRectLeftColumn R, v)) ∈
      fkRectTorusCutEdges R := by
    rw [mem_fkRectTorusCutEdges_iff]
    exact Or.inr ⟨rfl, rfl⟩
  have hclosedEdges := (fkRectCutClosedConfiguration_iff R eta).1 hclosed
  have hprimal : eta (fkRectDualEdgeToEdge R e) = false := by
    rw [hecross]
    exact hclosedEdges _ hecut
  have hopen : fkRectDualConfigurationEquiv R eta e = true := by
    rw [fkRectDualConfigurationEquiv_apply, hprimal]
    rfl
  refine ⟨e, hopen, ?_⟩
  simp only [e, fkRectTorusIndexedEdge, ↓reduceIte]
  rw [fkRect_cyclicPred_eq_of_val_succ R.height_pos huv]
  simp [Sym2.eq_swap]



theorem fkRectDualOpenGraph_rightBoundary_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectCutClosedConfiguration R eta)
    (u v : Fin R.height) :
    (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta)).Reachable
      (fkRectRightColumn R, u) (fkRectRightColumn R, v) := by
  let H : SimpleGraph (Fin R.height) :=
    SimpleGraph.comap (fun y => (fkRectRightColumn R, y))
      (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta))
  have hpath : pathGraph R.height ≤ H := by
    intro y z hyz
    rw [pathGraph_adj] at hyz
    change (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta)).Adj
      (fkRectRightColumn R, y) (fkRectRightColumn R, z)
    rcases hyz with hyz | hyz
    · exact fkRectDualOpenGraph_adj_right_of_val_succ R eta hclosed hyz
    · exact (fkRectDualOpenGraph_adj_right_of_val_succ
        R eta hclosed hyz).symm
  have huv : H.Reachable u v :=
    ((pathGraph_preconnected R.height).mono hpath) u v
  let f : H →g fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta) :=
    ⟨fun y => (fkRectRightColumn R, y), fun hyz => hyz⟩
  exact huv.map f



theorem fkRectRawHorizontalCrossingClusterCount_dual_le_one
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectCutClosedConfiguration R eta) :
    fkRectRawHorizontalCrossingClusterCount R
      (fkRectDualConfigurationEquiv R eta) ≤ 1 := by
  classical
  unfold fkRectRawHorizontalCrossingClusterCount
  rw [Fintype.card_le_one_iff_subsingleton]
  constructor
  intro C D
  apply Subtype.ext
  rcases C.2.2 with ⟨z, hz⟩
  rcases D.2.2 with ⟨w, hw⟩
  exact hz.symm.trans
    ((SimpleGraph.ConnectedComponent.sound
      (fkRectDualOpenGraph_rightBoundary_reachable R eta hclosed z w)).trans hw)



theorem fkRectRawPrimalDualHorizontalCrossingClusterCount_le_primal_add_one
    (R : FKRectTorus) (eta : R.Configuration)
    (hclosed : FKRectCutClosedConfiguration R eta) :
    fkRectRawPrimalDualHorizontalCrossingClusterCount R eta ≤
      fkRectRawHorizontalCrossingClusterCount R eta + 1 := by
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount
  exact Nat.add_le_add_left
    (fkRectRawHorizontalCrossingClusterCount_dual_le_one R eta hclosed) _

theorem fkRectCriticalCutFreeEventMass_mono
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {A B : Set R.Configuration} (hAB : A ⊆ B) :
    fkRectCriticalCutFreeEventMass R q A ≤
      fkRectCriticalCutFreeEventMass R q B := by
  unfold fkRectCriticalCutFreeEventMass
  apply div_le_div_of_nonneg_right
  · apply fkRectCriticalEventMass_mono R (by linarith)
    intro eta heta
    exact ⟨heta.1, hAB heta.2⟩
  · exact (fkRectCriticalClosedMass_cut_pos R hq).le

theorem fkRectCriticalCutFreeEventMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    0 ≤ fkRectCriticalCutFreeEventMass R q A := by
  unfold fkRectCriticalCutFreeEventMass
  exact div_nonneg
    (fkRectCriticalEventMass_nonneg R (by linarith) _)
    (fkRectCriticalClosedMass_cut_pos R hq).le

theorem fkRectCriticalClosedMass_cut_le_one
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) :
    fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) ≤ 1 := by
  rw [← fkRectCriticalEventMass_cutClosed_eq_closedMass]
  calc
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta} ≤
      fkRectCriticalEventMass R q Set.univ :=
        fkRectCriticalEventMass_mono R (by linarith) (Set.subset_univ _)
    _ = 1 := by
      unfold fkRectCriticalEventMass
      simpa using sum_fkRectCriticalRandomClusterProb R (by linarith)



theorem fkRectCriticalCutFree_primalDualCrossingTail_le_primalTail
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n + 1 <
          fkRectRawPrimalDualHorizontalCrossingClusterCount R
            (fkRectForceCutClosed R eta)} ≤
      fkRectCriticalCutFreeEventMass R q
        {eta | n < fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R eta)} := by
  apply fkRectCriticalCutFreeEventMass_mono R hq
  intro eta heta
  change n + 1 < fkRectRawPrimalDualHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R eta) at heta
  change n < fkRectRawHorizontalCrossingClusterCount R
    (fkRectForceCutClosed R eta)
  have hbound :=
    fkRectRawPrimalDualHorizontalCrossingClusterCount_le_primal_add_one
      R (fkRectForceCutClosed R eta)
        (fkRectCutClosedConfiguration_forceCutClosed R eta)
  omega


theorem fkRectCriticalCutFree_primalDualCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n + 1 <
          fkRectRawPrimalDualHorizontalCrossingClusterCount R
            (fkRectForceCutClosed R eta)} ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
  exact (fkRectCriticalCutFree_primalDualCrossingTail_le_primalTail
    R hq n).trans
      (fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow R hq n)

end

end StatMech.FrontierD
