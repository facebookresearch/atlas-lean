/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulShearCoordinates
import Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Code.FrontierD.FKRectRefinedDualOpenWalkCarrier



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section



private theorem fkRectSquareLiftStep_fst_eq_val_of_support_columnZeroBand
    (R : FKRectTorus) (right : Nat) (hproper : right + 1 < R.width)
    {x y : R.Vertex}
    {p q : Int × Int}
    (hdisp : q - p = fkRectDevelopedStep R x y)
    (hxright : x.1.val <= right) (hyright : y.1.val <= right)
    (hpcol : p.1 = (x.1.val : Int)) :
    q.1 = (y.1.val : Int) := by
  have hnot : ¬ fkRectCrossesHorizontalSeam R s(x, y) := by
    rw [fkRectCrossesHorizontalSeam_mk]
    push Not
    constructor <;> omega
  have hinc : fkRectHorizontalSeamIncrement R x y = 0 := by
    unfold fkRectHorizontalSeamIncrement
    by_cases hxy' : x.1.val + 1 = R.width ∧ y.1.val = 0
    · exact (hnot (Or.inr ⟨hxy'.2, hxy'.1⟩)).elim
    · by_cases hyx : x.1.val = 0 ∧ y.1.val + 1 = R.width
      · exact (hnot (Or.inl hyx)).elim
      · simp [hxy', hyx]
  have hfirst := congrArg Prod.fst hdisp
  simp only [Prod.fst_sub, fkRectDevelopedStep] at hfirst
  rw [hinc] at hfirst
  simp only [mul_zero, add_zero] at hfirst
  omega



theorem fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
    (p : Int × Int) (right : Nat)
    (hleft : 0 <= p.1) (hright : p.1 <= right) :
    8 <= (fkRectFaithfulShearPoint
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))) 0 ∧
      (fkRectFaithfulShearPoint
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))) 0 <=
          16 * (right : Int) + 16 := by
  rw [fkRectFaithfulShearPoint_refinedDualScale_eq]
  have h := fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds
    p 0 right hleft hright
  simp only [Matrix.cons_val_zero]
  omega

private theorem fkRectRefinedDualScale_develop_add_period_confinement
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectRefinedDualScalePoint
        (fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2)) =
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          (fkRectRefinedDeckTranslation R u).1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          (fkRectRefinedDeckTranslation R u).2) := by
  have h := fkRectSquareDevelopPoint_add_period R p u
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;>
    simp [fkRectRefinedDualScalePoint,
      fkRectRefinedDeckTranslation] at hx hy ⊢ <;> linarith



theorem FKRectRefinedDualOpenWalkBlocksAlong.faithfulRoute_fst_bounds
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l)
    (right : Nat) (hproper : right + 1 < R.width)
    (hsupport : ∀ v ∈ w.support, v.1.val <= right)
    (hpcol : p.1 = (x.1.val : Int))
    {d : FKRectIntegralSquareDart} (hd : d ∈ l)
    {r : Int × Int} (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    8 <= r.1 ∧ r.1 <= 16 * (right : Int) + 16 := by
  induction h with
  | nil p hp => simp at hd
  | @consForward x y z hxy w e u he p q s hp hq hpDeck hqDeck
      hdisp haxis l tail ih =>
      have hxright := hsupport x (by simp)
      have hyright := hsupport y (by simp)
      have hqcol := fkRectSquareLiftStep_fst_eq_val_of_support_columnZeroBand
        R right hproper hdisp hxright hyright hpcol
      have htailSupport : ∀ v ∈ w.support, v.1.val <= right := by
        intro v hv
        exact hsupport v (by simp [hv])
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · let t := fkRectRefinedDeckTranslation R u
        have hbetween :=
          fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between
            R e t d r (by simpa [t, fkRectRefinedDeckTranslation] using hd) hr
        have hpBound :=
          fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
            p right (by omega) (by rw [hpcol]; exact_mod_cast hxright)
        have hqBound :=
          fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
            q right (by omega) (by rw [hqcol]; exact_mod_cast hyright)
        have hstart :
            (fkRectFaithfulShearPair
              ((fkRectRefinedDualEdgeStart R e).1 + t.1,
                (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 =
              (fkRectFaithfulShearPoint
                (fkRectRefinedDualScalePoint
                  (fkRectSquareDevelopPoint p))) 0 := by
          rw [hpDeck]
          change (fkRectFaithfulShearPoint
              ((fkRectRefinedDualEdgeStart R e).1 + t.1,
                (fkRectRefinedDualEdgeStart R e).2 + t.2)) 0 = _
          rw [fkRectRefinedDualScale_develop_add_period_confinement]
          rfl
        have hend :
            (fkRectFaithfulShearPair
              ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
                (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 =
              (fkRectFaithfulShearPoint
                (fkRectRefinedDualScalePoint
                  (fkRectSquareDevelopPoint q))) 0 := by
          rw [hqDeck]
          change (fkRectFaithfulShearPoint
              ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
                (fkRectRefinedDualEdgeEnd R e).2 + t.2)) 0 = _
          rw [fkRectRefinedDualScale_develop_add_period_confinement]
          rfl
        rw [hstart, hend] at hbetween
        omega
      · exact ih htailSupport hqcol hd
  | @consReverse x y z hxy w e u he p q s hp hq hpDeck hqDeck
      hdisp haxis l tail ih =>
      have hxright := hsupport x (by simp)
      have hyright := hsupport y (by simp)
      have hqcol := fkRectSquareLiftStep_fst_eq_val_of_support_columnZeroBand
        R right hproper hdisp hxright hyright hpcol
      have htailSupport : ∀ v ∈ w.support, v.1.val <= right := by
        intro v hv
        exact hsupport v (by simp [hv])
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · let t := fkRectRefinedDeckTranslation R u
        have hbetween :=
          fkRectRefinedDualEdgeReverseBlock_faithfulRoute_fst_between
            R e t d r (by simpa [t, fkRectRefinedDeckTranslation] using hd) hr
        have hpBound :=
          fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
            p right (by omega) (by rw [hpcol]; exact_mod_cast hxright)
        have hqBound :=
          fkRectFaithfulShearPoint_refinedDualScale_develop_fst_bounds
            q right (by omega) (by rw [hqcol]; exact_mod_cast hyright)
        have hstart :
            (fkRectFaithfulShearPair
              ((fkRectRefinedDualEdgeStart R e).1 + t.1,
                (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 =
              (fkRectFaithfulShearPoint
                (fkRectRefinedDualScalePoint
                  (fkRectSquareDevelopPoint q))) 0 := by
          rw [hqDeck]
          change (fkRectFaithfulShearPoint
              ((fkRectRefinedDualEdgeStart R e).1 + t.1,
                (fkRectRefinedDualEdgeStart R e).2 + t.2)) 0 = _
          rw [fkRectRefinedDualScale_develop_add_period_confinement]
          rfl
        have hend :
            (fkRectFaithfulShearPair
              ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
                (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 =
              (fkRectFaithfulShearPoint
                (fkRectRefinedDualScalePoint
                  (fkRectSquareDevelopPoint p))) 0 := by
          rw [hpDeck]
          change (fkRectFaithfulShearPoint
              ((fkRectRefinedDualEdgeEnd R e).1 + t.1,
                (fkRectRefinedDualEdgeEnd R e).2 + t.2)) 0 = _
          rw [fkRectRefinedDualScale_develop_add_period_confinement]
          rfl
        rw [hstart, hend] at hbetween
        omega
      · exact ih htailSupport hqcol hd



theorem exists_fkRectRefinedDualOpenWalkFaithfulShear_fst_bounds
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Walk x y}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (hpath : FKRectIntegralSquareDartPath
      (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
      (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l)
    (halong : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l)
    (hlne : l ≠ [])
    (right : Nat) (hproper : right + 1 < R.width)
    (hsupport : ∀ v ∈ w.support, v.1.val <= right)
    (hpcol : p.1 = (x.1.val : Int)) :
    ∃ W : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint
          (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)))
        (fkRectFaithfulShearPoint
          (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q))),
      ∀ z ∈ W.support,
        8 <= z 0 ∧ z 0 <= 16 * (right : Int) + 16 := by
  obtain ⟨W, hW⟩ := hpath.exists_faithfulShearWalk_of_ne_nil hlne
  refine ⟨W, ?_⟩
  intro z hz
  obtain ⟨d, hdl, r, hr, rfl⟩ := hW z hz
  simpa [fkRectPairSite] using
    halong.faithfulRoute_fst_bounds R omega right hproper
      hsupport hpcol hdl hr

end

end StatMech.FrontierD
