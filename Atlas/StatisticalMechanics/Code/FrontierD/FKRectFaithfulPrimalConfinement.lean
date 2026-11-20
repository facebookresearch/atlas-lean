/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulShearCoordinates
import Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Code.FrontierD.FKRectRefinedOpenWalkProvenance



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

private theorem fkRectRefinedScale_develop_add_period_confinement
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectRefinedScalePoint
        (fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2)) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          4 * (fkRectSquareDeckTranslation R u).2) := by
  have h := fkRectSquareDevelopPoint_add_period R p u
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;>
    simp [fkRectRefinedScalePoint] at hx hy ⊢ <;> linarith




theorem FKRectRefinedOpenWalkBlocksAlong.faithfulRoute_fst_bounds
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
    (right : Nat)
    (hsupport : ∀ v ∈ w.support,
      1 ≤ v.1.val ∧ v.1.val ≤ right)
    (hpcol : p.1 = (x.1.val : Int))
    {d : FKRectIntegralSquareDart} {s : Int × Int}
    (hd : d ∈ l) (hs : s ∈ fkRectFaithfulShearDartRoute d) :
    16 ≤ s.1 ∧ s.1 ≤ 16 * (right : Int) + 8 := by
  induction h with
  | nil p hp => simp at hd
  | @consForward x y z hxy w e u he p q r hp hq hpDeck hqDeck
      hdisp haxis l tail ih =>
      have hxBand := hsupport x (by simp)
      have hyBand := hsupport y (by simp)
      have htailSupport : ∀ v ∈ w.support,
          1 ≤ v.1.val ∧ v.1.val ≤ right := by
        intro v hv
        exact hsupport v (by simp [hv])
      have hone : FKRectSquareWalkLift R
          (Walk.cons hxy (Walk.nil :
            (fkRectOpenGraph R
              (fkRectConfigurationOfEdges R F)).Walk y y)) p q :=
        FKRectSquareWalkLift.cons hp hq hdisp haxis
          (FKRectSquareWalkLift.nil q hq)
      have hqcol : q.1 = (y.1.val : Int) := by
        apply hone.end_fst_eq_val_of_support_positiveColumnBand R right
        · intro v hv
          simp only [Walk.support_cons, Walk.support_nil,
            List.mem_cons, List.mem_singleton] at hv
          rcases hv with rfl | hv
          · exact hxBand
          · rcases hv with rfl | hv
            · exact hyBand
            · simp at hv
        · exact hpcol
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · let t : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2)
        have hblock :=
          fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between
            R e t d s hd hs
        have hstart :
            ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
              (fkRectRefinedPrimalEdgeStart R e).2 + t.2) =
              fkRectRefinedScalePoint (fkRectSquareDevelopPoint p) := by
          rw [hpDeck,
            fkRectRefinedScale_develop_add_period_confinement]
          rfl
        have hend :
            ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
              (fkRectRefinedPrimalEdgeEnd R e).2 + t.2) =
              fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) := by
          rw [hqDeck,
            fkRectRefinedScale_develop_add_period_confinement]
          rfl
        rw [hstart, hend] at hblock
        change min
            ((fkRectFaithfulShearPoint
              (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0)
            ((fkRectFaithfulShearPoint
              (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 0) ≤
              s.1 ∧
            s.1 ≤ max
              ((fkRectFaithfulShearPoint
                (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0)
              ((fkRectFaithfulShearPoint
                (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 0)
            at hblock
        have hpBounds :=
          fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
            p 1 right (by omega) (by omega)
        have hqBounds :=
          fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
            q 1 right (by omega) (by omega)
        constructor
        · exact le_trans (le_min hpBounds.1 hqBounds.1) hblock.1
        · exact le_trans hblock.2 (max_le hpBounds.2 hqBounds.2)
      · exact ih htailSupport hqcol hd
  | @consReverse x y z hxy w e u he p q r hp hq hpDeck hqDeck
      hdisp haxis l tail ih =>
      have hxBand := hsupport x (by simp)
      have hyBand := hsupport y (by simp)
      have htailSupport : ∀ v ∈ w.support,
          1 ≤ v.1.val ∧ v.1.val ≤ right := by
        intro v hv
        exact hsupport v (by simp [hv])
      have hone : FKRectSquareWalkLift R
          (Walk.cons hxy (Walk.nil :
            (fkRectOpenGraph R
              (fkRectConfigurationOfEdges R F)).Walk y y)) p q :=
        FKRectSquareWalkLift.cons hp hq hdisp haxis
          (FKRectSquareWalkLift.nil q hq)
      have hqcol : q.1 = (y.1.val : Int) := by
        apply hone.end_fst_eq_val_of_support_positiveColumnBand R right
        · intro v hv
          simp only [Walk.support_cons, Walk.support_nil,
            List.mem_cons, List.mem_singleton] at hv
          rcases hv with rfl | hv
          · exact hxBand
          · rcases hv with rfl | hv
            · exact hyBand
            · simp at hv
        · exact hpcol
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · let t : Int × Int :=
          (4 * (fkRectSquareDeckTranslation R u).1,
            4 * (fkRectSquareDeckTranslation R u).2)
        have hblock :=
          fkRectRefinedPrimalEdgeReverseBlock_faithfulRoute_fst_between
            R e t d s hd hs
        have hstart :
            ((fkRectRefinedPrimalEdgeStart R e).1 + t.1,
              (fkRectRefinedPrimalEdgeStart R e).2 + t.2) =
              fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) := by
          rw [hqDeck,
            fkRectRefinedScale_develop_add_period_confinement]
          rfl
        have hend :
            ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1,
              (fkRectRefinedPrimalEdgeEnd R e).2 + t.2) =
              fkRectRefinedScalePoint (fkRectSquareDevelopPoint p) := by
          rw [hpDeck,
            fkRectRefinedScale_develop_add_period_confinement]
          rfl
        rw [hstart, hend] at hblock
        change min
            ((fkRectFaithfulShearPoint
              (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 0)
            ((fkRectFaithfulShearPoint
              (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0) ≤
              s.1 ∧
            s.1 ≤ max
              ((fkRectFaithfulShearPoint
                (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))) 0)
              ((fkRectFaithfulShearPoint
                (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0)
            at hblock
        have hpBounds :=
          fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
            p 1 right (by omega) (by omega)
        have hqBounds :=
          fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
            q 1 right (by omega) (by omega)
        constructor
        · exact le_trans (le_min hqBounds.1 hpBounds.1) hblock.1
        · exact le_trans hblock.2 (max_le hqBounds.2 hpBounds.2)
      · exact ih htailSupport hqcol hd



theorem FKRectRefinedOpenWalkBlocksAlong.exists_faithfulShearWalk_fst_bounds
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (halong : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
    (hpath : FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l)
    (hl : l ≠ []) (right : Nat)
    (hsupport : ∀ v ∈ w.support,
      1 ≤ v.1.val ∧ v.1.val ≤ right)
    (hpcol : p.1 = (x.1.val : Int)) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)))
        (fkRectFaithfulShearPoint
          (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q))),
      ∀ z ∈ V.support,
        16 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 8 := by
  obtain ⟨V, hV⟩ := hpath.exists_faithfulShearWalk_of_ne_nil hl
  refine ⟨V, ?_⟩
  intro z hz
  obtain ⟨d, hd, r, hr, rfl⟩ := hV z hz
  simpa [fkRectPairSite] using
    halong.faithfulRoute_fst_bounds R F right hsupport hpcol hd hr

end

end StatMech.FrontierD
