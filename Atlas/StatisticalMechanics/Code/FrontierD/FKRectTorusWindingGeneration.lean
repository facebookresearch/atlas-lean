/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusWindingInsertion

open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectStepWinding (R : FKRectTorus) (x y : R.Vertex) : Int × Int :=
  (fkRectHorizontalSeamIncrement R x y,
    fkRectVerticalSeamIncrement R x y)

theorem fkRectStepWinding_swap (R : FKRectTorus) (x y : R.Vertex) :
    fkRectStepWinding R y x = -fkRectStepWinding R x y := by
  ext
  · exact fkRectHorizontalSeamIncrement_swap R x y
  · exact fkRectVerticalSeamIncrement_swap R x y



theorem fkRectWalkWinding_insert_eq_old_add_zsmul
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    {u v : R.Vertex}
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Walk u v) :
    ∃ q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk u v,
      ∃ n : Int,
        fkRectWalkWinding R p =
          fkRectWalkWinding R q +
            n • fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r) := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  let H := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hab : fkRectTorusIndexedEdge R e = s(a, b) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R e
  have hgraph : H = G ⊔ SimpleGraph.edge a b :=
    fkRectOpenGraph_configurationOfEdges_insert R F e hab
  have hfund : fkRectWalkWinding R
      (fkRectInsertedFundamentalWalk R F e r) =
        fkRectWalkWinding R r + fkRectStepWinding R b a := by
    rw [fkRectInsertedFundamentalWalk_winding]
    rfl
  induction p with
  | nil =>
      refine ⟨.nil, 0, ?_⟩
      simp [fkRectWalkWinding]
  | @cons x y z hxy p ih =>
      obtain ⟨q, n, hn⟩ := ih
      have hxy' : (G ⊔ SimpleGraph.edge a b).Adj x y := by
        rw [← hgraph]
        exact hxy
      rw [SimpleGraph.sup_adj] at hxy'
      rcases hxy' with hold | hnew
      · refine ⟨.cons hold q, n, ?_⟩
        simp only [fkRectWalkWinding]
        rw [hn]
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul] <;> ring
      · rw [SimpleGraph.edge_adj] at hnew
        rcases hnew.1 with hforward | hreverse
        · rcases hforward with ⟨rfl, rfl⟩
          refine ⟨r.append q, n - 1, ?_⟩
          simp only [fkRectWalkWinding, fkRectWalkWinding_append]
          rw [hn, hfund]
          have hswap := fkRectStepWinding_swap R a b
          apply Prod.ext
          · have hx := congrArg Prod.fst hswap
            simp only [Prod.fst_neg] at hx
            simp only [Prod.fst_add, Prod.smul_fst, zsmul_eq_mul]
            dsimp [fkRectStepWinding] at hx ⊢
            ring_nf at hx ⊢
            linear_combination hx
          · have hy := congrArg Prod.snd hswap
            simp only [Prod.snd_neg] at hy
            simp only [Prod.snd_add, Prod.smul_snd, zsmul_eq_mul]
            dsimp [fkRectStepWinding] at hy ⊢
            ring_nf at hy ⊢
            linear_combination hy
        · rcases hreverse with ⟨rfl, rfl⟩
          refine ⟨r.reverse.append q, n + 1, ?_⟩
          simp only [fkRectWalkWinding, fkRectWalkWinding_append,
            fkRectWalkWinding_reverse]
          rw [hn, hfund]
          apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
            Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd,
            zsmul_eq_mul, Prod.fst_mul, Prod.snd_mul,
            Prod.fst_intCast, Prod.snd_intCast, Int.cast_id,
            fkRectStepWinding] <;>
            ring



theorem fkRectClosedWindingSubgroup_insert_le_sup_zmultiples
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
    fkRectClosedWindingSubgroup R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkRectMedialWestPrimal R e) ≤
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F)
          (fkRectMedialWestPrimal R e) ⊔
        AddSubgroup.zmultiples (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) := by
  rintro w ⟨p, rfl⟩
  obtain ⟨q, n, hn⟩ :=
    fkRectWalkWinding_insert_eq_old_add_zsmul R F e r p
  rw [hn]
  exact AddSubgroup.add_mem _
    (show fkRectWalkWinding R q ∈
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F)
        (fkRectMedialWestPrimal R e) ⊔
          AddSubgroup.zmultiples (fkRectWalkWinding R
            (fkRectInsertedFundamentalWalk R F e r)) from
      AddSubgroup.mem_sup_left ⟨q, rfl⟩)
    (show n • fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r) ∈
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F)
          (fkRectMedialWestPrimal R e) ⊔
        AddSubgroup.zmultiples (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r)) from
      AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem _
        (AddSubgroup.mem_zmultiples _) n))

end

end StatMech.FrontierD
