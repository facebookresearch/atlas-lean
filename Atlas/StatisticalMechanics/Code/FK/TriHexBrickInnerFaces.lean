/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexBrickFaces









open Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

def triHexBrickInnerCell {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1, fun k => by
    have hk := t.2 k
    exact Nat.le_trans hk (Nat.le_of_lt hNm)⟩

def triHexBrickInnerPred0 {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1 - hexagonalStep 0, by
    intro k
    have ht := t.2 k
    fin_cases k <;>
      simp [hexagonalStep] at ht ⊢ <;> omega⟩

def triHexBrickInnerPred1 {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1 - hexagonalStep 1, by
    intro k
    have ht := t.2 k
    fin_cases k <;>
      simp [hexagonalStep] at ht ⊢ <;> omega⟩

private theorem face_site_eq_of_coords {x y : Site 2}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext k
  fin_cases k <;> assumption



theorem triHexBrickInner_faceRegion_adj_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (f g : Site 2)
    (hf : f = hexagonalBrickFaceLeft t.1 ∨
      f = hexagonalBrickFaceRight t.1) :
    (whb_faceRegion (imageGraph (triHexPlanarFiniteStarPlanar m))).Adj f g ↔
      (f = hexagonalBrickFaceLeft t.1 ∧
          g = hexagonalBrickFaceRight t.1) ∨
        (f = hexagonalBrickFaceRight t.1 ∧
          g = hexagonalBrickFaceLeft t.1) := by
  have ht0 : Matrix.vecHead t.1 = t.1 0 := rfl
  have ht1 : Matrix.vecHead (Matrix.vecTail t.1) = t.1 1 := rfl
  constructor
  · intro hfg
    rcases hf with rfl | rfl
    · by_cases hg : g = hexagonalBrickFaceRight t.1
      · exact Or.inl ⟨rfl, hg⟩
      · exfalso
        apply hfg.2
        rcases adj_cases hfg.1.symm with
            ⟨h0, hplus | hminus⟩ | ⟨h1, hplus | hminus⟩
        · have hgtop : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred1 hNm t).1 1 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hplus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred1 hNm t).1 1 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgtop, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred1 hNm t) 1
        · have hgbottom : g = triHexBrickSpokeFlank2
              (triHexBrickInnerPred0 hNm t).1 2 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hminus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank1
                (triHexBrickInnerPred0 hNm t).1 2 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [hgbottom, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred0 hNm t) 2
        · have hgright : g = hexagonalBrickFaceRight t.1 := by
            apply face_site_eq_of_coords <;>
              simp [hexagonalBrickFaceLeft,
                hexagonalBrickFaceRight, ht0, ht1] at h1 hplus ⊢ <;> omega
          exact (hg hgright).elim
        · have hgleft : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred0 hNm t).1 0 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h1 hminus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred0 hNm t).1 0 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgleft, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred0 hNm t) 0
    · by_cases hg : g = hexagonalBrickFaceLeft t.1
      · exact Or.inr ⟨rfl, hg⟩
      · exfalso
        apply hfg.2
        rcases adj_cases hfg.1.symm with
            ⟨h0, hplus | hminus⟩ | ⟨h1, hplus | hminus⟩
        · have hgtop : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred1 hNm t).1 2 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hplus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred1 hNm t).1 2 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred1,
                hexagonalBrickFaceRight, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgtop, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred1 hNm t) 2
        · have hgbottom : g = triHexBrickSpokeFlank2 t.1 1 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hminus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank1 t.1 1 := by rfl
          rw [hgbottom, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerCell hNm t) 1
        · have hgright : g = triHexBrickSpokeFlank2 t.1 0 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h1 hplus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank1 t.1 0 := by rfl
          rw [hgright, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerCell hNm t) 0
        · have hgleft : g = hexagonalBrickFaceLeft t.1 := by
            apply face_site_eq_of_coords <;>
              simp [hexagonalBrickFaceLeft,
                hexagonalBrickFaceRight, ht0, ht1] at h1 hminus ⊢ <;> omega
          exact (hg hgleft).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [whb_faceRegion_adj]
      exact ⟨hexagonalBrickFaces_adj t.1,
        triHexPlanarFiniteStar_middle_not_mem_imageGraph m t.1⟩
    · exact (show
        (whb_faceRegion (imageGraph
          (triHexPlanarFiniteStarPlanar m))).Adj
            (hexagonalBrickFaceLeft t.1)
            (hexagonalBrickFaceRight t.1) from
          (whb_faceRegion_adj _ _ _).2
            ⟨hexagonalBrickFaces_adj t.1,
              triHexPlanarFiniteStar_middle_not_mem_imageGraph m t.1⟩).symm

private theorem triHexBrickInner_reachable_preserves
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) {f g : Site 2}
    (hf : f = hexagonalBrickFaceLeft t.1 ∨
      f = hexagonalBrickFaceRight t.1)
    (hfg : (whb_faceRegion
      (imageGraph (triHexPlanarFiniteStarPlanar m))).Reachable f g) :
    g = hexagonalBrickFaceLeft t.1 ∨
      g = hexagonalBrickFaceRight t.1 := by
  rcases hfg with ⟨w⟩
  induction w with
  | nil => exact hf
  | @cons a b c hab w ih =>
      have hb := (triHexBrickInner_faceRegion_adj_iff
        hNm t a b hf).mp hab
      have hb' : b = hexagonalBrickFaceLeft t.1 ∨
          b = hexagonalBrickFaceRight t.1 := by
        rcases hb with ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inr h
        · exact Or.inl h
      exact ih hb'



theorem triHexPlanarFiniteStar_pfdFace_eq_inner_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (f : Site 2) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar m) f =
        triHexPlanarFiniteStarFace m t.1 ↔
      f = hexagonalBrickFaceLeft t.1 ∨
        f = hexagonalBrickFaceRight t.1 := by
  constructor
  · intro hface
    have hreach : (whb_faceRegion
        (imageGraph (triHexPlanarFiniteStarPlanar m))).Reachable
          (hexagonalBrickFaceLeft t.1) f := by
      exact (ConnectedComponent.eq.mp hface).symm
    exact triHexBrickInner_reachable_preserves hNm t (Or.inl rfl) hreach
  · rintro (rfl | rfl)
    · rfl
    · exact (triHexPlanarFiniteStar_pfdFace_left_eq_right m t.1).symm



def triHexBrickInnerFaceMap (N m : Nat) :
    {z : Site 2 // z ∈ box 2 N} →
      kwg_Face (triHexPlanarFiniteStarPlanar m) :=
  fun t => triHexPlanarFiniteStarFace m t.1

theorem triHexBrickInnerFaceMap_injective
    {N m : Nat} (hNm : N < m) :
    Function.Injective (triHexBrickInnerFaceMap N m) := by
  intro t u htu
  have hrep : BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar m)
      (hexagonalBrickFaceLeft t.1) =
      triHexPlanarFiniteStarFace m u.1 := htu
  rcases (triHexPlanarFiniteStar_pfdFace_eq_inner_iff
    hNm u (hexagonalBrickFaceLeft t.1)).mp hrep with hleft | hright
  · apply Subtype.ext
    have h1 : t.1 1 = u.1 1 := by
      have := congrFun hleft 1
      simp [hexagonalBrickFaceLeft] at this
      omega
    have h0 : t.1 0 = u.1 0 := by
      have := congrFun hleft 0
      simp [hexagonalBrickFaceLeft] at this
      omega
    exact face_site_eq_of_coords h0 h1
  · have h1 : t.1 1 = u.1 1 := by
      have := congrFun hright 1
      simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] at this
      omega
    have hbad := congrFun hright 0
    simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight, h1] at hbad
    omega

theorem triHexPlanarFiniteStarFace_eq_inner_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (u : Site 2) :
    triHexPlanarFiniteStarFace m u =
        triHexPlanarFiniteStarFace m t.1 ↔ u = t.1 := by
  constructor
  · intro hface
    rcases (triHexPlanarFiniteStar_pfdFace_eq_inner_iff hNm t
      (hexagonalBrickFaceLeft u)).mp hface with hleft | hright
    · have h1 : u 1 = t.1 1 := by
        have := congrFun hleft 1
        simp [hexagonalBrickFaceLeft] at this
        omega
      have h0 : u 0 = t.1 0 := by
        have := congrFun hleft 0
        simp [hexagonalBrickFaceLeft] at this
        omega
      exact face_site_eq_of_coords h0 h1
    · have h1 : u 1 = t.1 1 := by
        have := congrFun hright 1
        simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight] at this
        omega
      have hbad := congrFun hright 0
      simp [hexagonalBrickFaceLeft, hexagonalBrickFaceRight, h1] at hbad
      omega
  · rintro rfl
    rfl


def triHexBrickInnerTriangleGraph (N : Nat) :
    SimpleGraph {z : Site 2 // z ∈ box 2 N} :=
  triangularGraph.induce (box 2 N)

noncomputable instance triHexBrickInnerTriangleGraphDecidable (N : Nat) :
    DecidableRel (triHexBrickInnerTriangleGraph N).Adj := Classical.decRel _


noncomputable def triHexBrickFullDualGraph (m : Nat) :
    SimpleGraph (kwg_Face (triHexPlanarFiniteStarPlanar m)) :=
  BeffaraDC.pfdClosedDual (triHexPlanarFiniteStarPlanar m) ⊥

noncomputable instance triHexBrickFullDualGraphDecidable (m : Nat) :
    DecidableRel (triHexBrickFullDualGraph m).Adj := Classical.decRel _

theorem triHexSpokeFaces_adj (z : Site 2) (i : Fin 3) :
    triangularGraph.Adj (triHexSpokeFace1 z i)
      (triHexSpokeFace2 z i) := by
  have hz0 : Matrix.vecHead z = z 0 := rfl
  have hz1 : Matrix.vecHead (Matrix.vecTail z) = z 1 := rfl
  rw [triangularGraph_adj]
  unfold triangularAdj
  fin_cases i
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨0, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨1, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨2, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]

private theorem triHexBrickFullDual_adj_of_spoke
    {N m : Nat} (hNm : N < m)
    (x y : {z : Site 2 // z ∈ box 2 N})
    (z : TriHexPlanarFiniteCell m) (i : Fin 3)
    (hpair : s(triHexSpokeFace1 z.1 i, triHexSpokeFace2 z.1 i) =
      s(x.1, y.1)) :
    (triHexBrickFullDualGraph m).Adj
      (triHexBrickInnerFaceMap N m x)
      (triHexBrickInnerFaceMap N m y) := by
  rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj]
  refine ⟨fun h => ?_, triHexPlanarFiniteStarEdgeEquiv m (z, i), by simp, ?_⟩
  · have hxy := triHexBrickInnerFaceMap_injective hNm h
    subst y
    rw [Sym2.eq_iff] at hpair
    rcases hpair with hpair | hpair
    · exact (triHexSpokeFaces_adj z.1 i).ne
        (hpair.1.trans hpair.2.symm)
    · exact (triHexSpokeFaces_adj z.1 i).ne
        (hpair.1.trans hpair.2.symm)
  · rw [triHexPlanarFiniteStar_dualEnds]
    simpa [triHexBrickInnerFaceMap] using congrArg
      (Sym2.map (triHexPlanarFiniteStarFace m)) hpair



theorem triHexBrickInnerFaceMap_adj
    {N m : Nat} (hNm : N < m)
    (x y : {z : Site 2 // z ∈ box 2 N}) :
    (triHexBrickInnerTriangleGraph N).Adj x y ↔
      (triHexBrickFullDualGraph m).Adj
        (triHexBrickInnerFaceMap N m x)
        (triHexBrickInnerFaceMap N m y) := by
  have hx0 : Matrix.vecHead x.1 = x.1 0 := rfl
  have hx1 : Matrix.vecHead (Matrix.vecTail x.1) = x.1 1 := rfl
  have hy0 : Matrix.vecHead y.1 = y.1 0 := rfl
  have hy1 : Matrix.vecHead (Matrix.vecTail y.1) = y.1 1 := rfl
  constructor
  · intro hxy
    change triangularGraph.Adj x.1 y.1 at hxy
    rw [triangularGraph_adj] at hxy
    rcases hxy with ⟨i, hpos | hneg⟩
    · fin_cases i
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerCell hNm x) 0
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerCell, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerCell hNm x) 1
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerCell, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerPred0 hNm x) 2
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerPred0, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
    · fin_cases i
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerCell hNm y) 0 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerCell, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff] at hneg ⊢ <;>
              omega)).symm
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerCell hNm y) 1 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerCell, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff] at hneg ⊢ <;>
              omega)).symm
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerPred0 hNm y) 2 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerPred0, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff]
                  at hneg ⊢ <;> omega)).symm
  · intro hxy
    rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj] at hxy
    obtain ⟨_, e, _, hends⟩ := hxy
    generalize ha : (triHexPlanarFiniteStarEdgeEquiv m).symm e = a
    rcases a with ⟨z, i⟩
    have he := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply e
    rw [ha] at he
    rw [← he, triHexPlanarFiniteStar_dualEnds] at hends
    rw [Sym2.eq_iff] at hends
    change triangularGraph.Adj x.1 y.1
    rcases hends with hends | hends
    · have hx : triHexSpokeFace1 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.1
      have hy : triHexSpokeFace2 z.1 i = y.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.2
      simpa [hx, hy] using triHexSpokeFaces_adj z.1 i
    · have hy : triHexSpokeFace1 z.1 i = y.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.1
      have hx : triHexSpokeFace2 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.2
      simpa [hx, hy] using (triHexSpokeFaces_adj z.1 i).symm

end

end StatMech.FK.PeriodicPlanar
