/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4SquareFaceEmbedding
import Code.OSSS.FKSharpnessWeightedDomain

open Finset Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section




def pfdEdgeBundle (P : PlanarZ2Subgraph) (a : Sym2 (kwg_Face P)) :
    Finset (kwg_Edge P) :=
  Finset.univ.filter (fun e => kwg_dualEnds P e = a)

@[simp] theorem mem_pfdEdgeBundle (P : PlanarZ2Subgraph)
    (a : Sym2 (kwg_Face P)) (e : kwg_Edge P) :
    e ∈ pfdEdgeBundle P a ↔ kwg_dualEnds P e = a := by
  simp [pfdEdgeBundle]




def pfdEffectiveParam (P : PlanarZ2Subgraph) (p : Real)
    (a : Sym2 (kwg_Face P)) : Real :=
  1 - (1 - p) ^ (pfdEdgeBundle P a).card


theorem pfdEdgeBundle_nonempty_of_fullDualEdge (P : PlanarZ2Subgraph)
    {a : Sym2 (kwg_Face P)}
    (ha : a ∈ (pfdClosedDual P ⊥).edgeSet) :
    (pfdEdgeBundle P a).Nonempty := by
  induction a using Sym2.inductionOn with
  | _ C D =>
      rw [SimpleGraph.mem_edgeSet, pfdClosedDual_adj] at ha
      obtain ⟨_, e, _, hends⟩ := ha
      exact ⟨e, (mem_pfdEdgeBundle P _ e).2 hends⟩

theorem pfdEffectiveParam_pos (P : PlanarZ2Subgraph)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    {a : Sym2 (kwg_Face P)}
    (ha : a ∈ (pfdClosedDual P ⊥).edgeSet) :
    0 < pfdEffectiveParam P p a := by
  have hcard : 0 < (pfdEdgeBundle P a).card :=
    Finset.card_pos.mpr (pfdEdgeBundle_nonempty_of_fullDualEdge P ha)
  have hbase : 0 ≤ 1 - p := by linarith
  have hlt : (1 - p) ^ (pfdEdgeBundle P a).card < 1 := by
    exact pow_lt_one₀ hbase (by linarith) hcard.ne'
  unfold pfdEffectiveParam
  linarith

theorem pfdEffectiveParam_lt_one (P : PlanarZ2Subgraph)
    {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (a : Sym2 (kwg_Face P)) :
    pfdEffectiveParam P p a < 1 := by
  unfold pfdEffectiveParam
  have hpow : 0 < (1 - p) ^ (pfdEdgeBundle P a).card :=
    pow_pos (by linarith) _
  linarith



theorem kwg_edge_eq_of_dualEnds_eq_inner
    {N m : Nat} (hNm : N < m)
    {x y : FK.boxVerts 2 N}
    (hxy : (FK.boxGraph 2 N).Adj x y)
    {e f : kwg_Edge (fkSquareBoxPlanar m)}
    (he : kwg_dualEnds (fkSquareBoxPlanar m) e =
      s(fkSquareBox_innerFaceMap N m x,
        fkSquareBox_innerFaceMap N m y))
    (hf : kwg_dualEnds (fkSquareBoxPlanar m) f =
      s(fkSquareBox_innerFaceMap N m x,
        fkSquareBox_innerFaceMap N m y)) :
    e = f := by
  let P := fkSquareBoxPlanar m
  have flank_eq (g : kwg_Edge P)
      (hg : kwg_dualEnds P g =
        s(fkSquareBox_innerFaceMap N m x,
          fkSquareBox_innerFaceMap N m y)) :
      s(kwg_flankLeft P g, kwg_flankRight P g) = s(x.1, y.1) := by
    change s(pfdFace P (kwg_flankLeft P g),
        pfdFace P (kwg_flankRight P g)) =
      s(pfdFace P x.1, pfdFace P y.1) at hg
    rw [Sym2.eq_iff] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inl ⟨(pfdFace_eq_inner_iff hNm x.2).mp hg.1,
        (pfdFace_eq_inner_iff hNm y.2).mp hg.2⟩
    · exact Or.inr ⟨(pfdFace_eq_inner_iff hNm y.2).mp hg.1,
        (pfdFace_eq_inner_iff hNm x.2).mp hg.2⟩
  have heflank := flank_eq e he
  have hfflank := flank_eq f hf
  apply Subtype.ext
  apply (Sym2.map.injective (fkSquareBoxPlanar m).emb.injective)
  calc
    Sym2.map (fkSquareBoxPlanar m).emb e.1 =
        sharedPrimalEdge (kwg_flankLeft P e) (kwg_flankRight P e) :=
      (kwg_flanks_shared P e).symm
    _ = sharedPrimalEdge x.1 y.1 :=
      (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e) hxy).mp heflank
    _ = sharedPrimalEdge (kwg_flankLeft P f) (kwg_flankRight P f) := by
      exact (jce_sharedPrimalEdge_inj hxy (kwg_flanks_adj P f)).mp
        hfflank.symm
    _ = Sym2.map (fkSquareBoxPlanar m).emb f.1 := kwg_flanks_shared P f



theorem pfdEdgeBundle_inner_card_eq_one
    {N m : Nat} (hNm : N < m)
    (a : (FK.boxGraph 2 N).edgeFinset) :
    (pfdEdgeBundle (fkSquareBoxPlanar m)
      (ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1)).card = 1 := by
  have haAdj : (FK.boxGraph 2 N).Adj a.1.out.1 a.1.out.2 := by
    have haEdge : a.1 ∈ (FK.boxGraph 2 N).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using a.2
    rw [← a.1.out_eq] at haEdge
    rw [SimpleGraph.mem_edgeSet] at haEdge
    exact haEdge
  have ha : (fkSquareBoxFullDualGraph m).Adj
      (fkSquareBox_innerFaceMap N m a.1.out.1)
      (fkSquareBox_innerFaceMap N m a.1.out.2) := by
    apply (fkSquareBox_innerFaceMap_adj hNm _ _).mp
    exact haAdj
  rw [fkSquareBoxFullDualGraph, pfdClosedDual_adj] at ha
  obtain ⟨_, e, _, he⟩ := ha
  have hout : ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1 =
      s(fkSquareBox_innerFaceMap N m a.1.out.1,
        fkSquareBox_innerFaceMap N m a.1.out.2) := by
    calc
      ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1 =
          ocd_innerEdge (fkSquareBox_innerFaceMap N m)
            s(a.1.out.1, a.1.out.2) :=
        congrArg (ocd_innerEdge (fkSquareBox_innerFaceMap N m))
          a.1.out_eq.symm
      _ = _ := ocd_innerEdge_mk _ _ _
  apply Finset.card_eq_one.mpr
  refine ⟨e, ?_⟩
  ext f
  rw [Finset.mem_singleton, mem_pfdEdgeBundle]
  constructor
  · intro hf
    exact kwg_edge_eq_of_dualEnds_eq_inner hNm
      haAdj
      (by simpa [hout] using hf) (by simpa [hout] using he)
  · rintro rfl
    simpa [hout] using he



theorem pfdEffectiveParam_innerEdge
    {N m : Nat} (hNm : N < m) (p : Real)
    (a : (FK.boxGraph 2 N).edgeFinset) :
    pfdEffectiveParam (fkSquareBoxPlanar m) p
      (ocd_innerEdge (fkSquareBox_innerFaceMap N m) a.1) = p := by
  rw [pfdEffectiveParam, pfdEdgeBundle_inner_card_eq_one hNm]
  ring

end

end StatMech.FrontierD
