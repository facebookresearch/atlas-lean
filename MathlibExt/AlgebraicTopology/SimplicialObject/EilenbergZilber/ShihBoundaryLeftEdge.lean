/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryEndpointCancellation
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleUnit

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber.ShihIndex

/-- The `p = 0` nonmixed active index in fixed total degree, with the unique
zero-left-degree shuffle before inserting its sole left position. -/
def leftEdgeIndex (N : ℕ) (q : Fin N) (a : Fin 2) : ShihIndex N where
  p := ⟨0, lt_of_le_of_lt (Nat.zero_le q.val) q.isLt⟩
  q := ⟨q.val, by
    change q.val < N
    exact q.isLt⟩
  shuffle := Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q) a

/-- The active face belonging to a `p = 0` left-edge index. -/
def leftEdgeFace (N : ℕ) (q : Fin N) (a : Fin 2) : Fin (N + 2) :=
  ⟨(leftEdgeIndex N q a).gap +
      (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q) a).val, by
    have hq := q.isLt
    have ha := a.isLt
    simp only [leftEdgeIndex, gap]
    omega⟩

@[simp]
theorem leftEdgeIndex_gap (N : ℕ) (q : Fin N) (a : Fin 2) :
    (leftEdgeIndex N q a).gap = N - q.val := by
  simp [leftEdgeIndex, gap]

@[simp]
theorem leftEdgeFace_zero (N : ℕ) (q : Fin N) :
    leftEdgeFace N q 0 = ⟨N - q.val, by omega⟩ := by
  apply Fin.ext
  simp [leftEdgeFace]

@[simp]
theorem leftEdgeFace_last (N : ℕ) (q : Fin N) :
    leftEdgeFace N q (Fin.last 1) = Fin.last (N + 1) := by
  apply Fin.ext
  simp only [leftEdgeFace, leftEdgeIndex_gap,
    Shuffle.leftBoundaryIndex_last, Fin.val_last]
  have hq := q.isLt
  omega

set_option backward.isDefEq.respectTransparency false in
theorem delta_leftEdgeLast_comp_leftHom_eq_zeroSucc
    (n : ℕ) (q : Fin n) :
    SimplexCategory.δ (leftEdgeFace (n + 1) q.castSucc (Fin.last 1)) ≫
        (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).leftHom =
      SimplexCategory.δ (leftEdgeFace (n + 1) q.succ 0) ≫
        (leftEdgeIndex (n + 1) q.succ 0).leftHom := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, ShihIndex.leftHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [leftEdgeFace_last, leftEdgeFace_zero]
  simp only [leftEdgeIndex_gap]
  have hq := q.isLt
  let g := n - q.val
  have hg : 0 < g := by simp only [g]; omega
  have hng : q.val + g = n := by simp only [g]; omega
  simp only [Fin.val_castSucc, Fin.val_succ]
  simp only [show n + 1 - q.val = g + 1 by simp only [g]; omega,
    show n + 1 - (q.val + 1) = g by simp only [g]; omega]
  change
    (if _h : ((Fin.last (n + 2)).succAbove x).val < g + 1 then _ else _) =
      (if _h : ((⟨g, by omega⟩ : Fin (n + 3)).succAbove x).val < g
        then _ else _)
  by_cases hx : x.val < g
  · have hlast : x.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last x
    have hzero : x.castSucc < (⟨g, by omega⟩ : Fin (n + 3)) := by
      exact hx
    rw [Fin.succAbove_of_castSucc_lt _ _ hlast,
      Fin.succAbove_of_castSucc_lt _ _ hzero]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left (by omega), dite_eq_left hx]
  · have hxg : g ≤ x.val := le_of_not_gt hx
    have hlast : x.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last x
    have hzero : (⟨g, by omega⟩ : Fin (n + 3)) ≤ x.castSucc := by
      exact hxg
    rw [Fin.succAbove_of_castSucc_lt _ _ hlast,
      Fin.succAbove_of_le_castSucc _ _ hzero]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hxeq : x.val = g
    · rw [dite_eq_left (by omega), dite_eq_right (by omega)]
      apply Fin.ext
      let z : Fin (0 + (q.val + 1) + 1) := ⟨0, by omega⟩
      have hsuffixZero :
          (leftEdgeIndex (n + 1) q.succ 0).gap ≤ x.succ.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_succ]
        omega
      have hinput :
          (leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
              (Fin.cast (by omega) z) := by
        apply Fin.ext
        change x.val + 1 - (leftEdgeIndex (n + 1) q.succ 0).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_zero,
          Fin.zero_succAbove]
        simp only [Fin.val_succ, Fin.val_cast, z]
        omega
      have hshuffle := Shuffle.leftHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle (q.val + 1)) (0 : Fin 2) z
      have hval := congrArg Fin.val hshuffle
      have hmapVal :
          ((leftEdgeIndex (n + 1) q.succ 0).shuffle.leftHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero)).val = 1 := by
        change
          ((Shuffle.leftBoundaryShuffle
              (Shuffle.leftUnitShuffle (q.val + 1)) 0).leftHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput
              x.succ hsuffixZero)).val = 1
        calc
          _ = ((Shuffle.leftBoundaryShuffle
                (Shuffle.leftUnitShuffle (q.val + 1)) 0).leftHom.toOrderHom
              ((Shuffle.leftBoundaryIndex
                  (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
                (Fin.cast (by omega) z))).val := by rw [hinput]
          _ = ((0 : Fin 2).succAbove
              ((Shuffle.leftUnitShuffle (q.val + 1)).leftHom.toOrderHom z)).val := hval
          _ = 1 := by
            simp [Shuffle.leftUnitShuffle_leftHom]
      change x.val = g - 1 + _
      rw [hmapVal]
      omega
    · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      apply Fin.ext
      let zLast : Fin (0 + q.val + 1) := ⟨x.val - (g + 1), by
        have hxlt := x.isLt
        change x.val < n + 2 at hxlt
        omega⟩
      let zZero : Fin (0 + (q.val + 1) + 1) := ⟨x.val - g, by
        have hxlt := x.isLt
        change x.val < n + 2 at hxlt
        omega⟩
      have hsuffixLast :
          (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).gap ≤
            x.castSucc.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_castSucc]
        omega
      have hsuffixZero :
          (leftEdgeIndex (n + 1) q.succ 0).gap ≤ x.succ.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_succ]
        omega
      have hinputLast :
          (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
              x.castSucc hsuffixLast =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q.val)
              (Fin.last 1)).succAbove (Fin.cast (by omega) zLast) := by
        apply Fin.ext
        change x.val - (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_last,
          Fin.succAbove_last]
        simp only [Fin.val_castSucc, Fin.val_cast, zLast]
        omega
      have hinputZero :
          (leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
              (Fin.cast (by omega) zZero) := by
        apply Fin.ext
        change x.val + 1 - (leftEdgeIndex (n + 1) q.succ 0).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_zero,
          Fin.zero_succAbove]
        simp only [Fin.val_succ, Fin.val_cast, zZero]
        omega
      have hshuffleLast := Shuffle.leftHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle q.val) (Fin.last 1) zLast
      have hshuffleZero := Shuffle.leftHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle (q.val + 1)) (0 : Fin 2) zZero
      have hvalLast := congrArg Fin.val hshuffleLast
      have hvalZero := congrArg Fin.val hshuffleZero
      have hmapLast :
          ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).shuffle.leftHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
              x.castSucc hsuffixLast)).val = 0 := by
        change ((Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
            (Fin.last 1)).leftHom.toOrderHom
          ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
            x.castSucc hsuffixLast)).val = 0
        calc
          _ = ((Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
                (Fin.last 1)).leftHom.toOrderHom
              ((Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q.val)
                (Fin.last 1)).succAbove (Fin.cast (by omega) zLast))).val := by
            rw [hinputLast]
          _ = ((Fin.last 1).succAbove
              ((Shuffle.leftUnitShuffle q.val).leftHom.toOrderHom zLast)).val := hvalLast
          _ = 0 := by
            simp [Shuffle.leftUnitShuffle_leftHom]
      have hmapZero :
          ((leftEdgeIndex (n + 1) q.succ 0).shuffle.leftHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero)).val = 1 := by
        change
          ((Shuffle.leftBoundaryShuffle
              (Shuffle.leftUnitShuffle (q.val + 1)) 0).leftHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput
              x.succ hsuffixZero)).val = 1
        calc
          _ = ((Shuffle.leftBoundaryShuffle
                (Shuffle.leftUnitShuffle (q.val + 1)) 0).leftHom.toOrderHom
              ((Shuffle.leftBoundaryIndex
                  (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
                (Fin.cast (by omega) zZero))).val := by rw [hinputZero]
          _ = ((0 : Fin 2).succAbove
              ((Shuffle.leftUnitShuffle (q.val + 1)).leftHom.toOrderHom zZero)).val := hvalZero
          _ = 1 := by
            simp [Shuffle.leftUnitShuffle_leftHom]
      change g + 1 - 1 + _ = g - 1 + _
      rw [hmapLast, hmapZero]
      omega

set_option backward.isDefEq.respectTransparency false in
theorem delta_leftEdgeLast_comp_rightHom_eq_zeroSucc
    (n : ℕ) (q : Fin n) :
    SimplexCategory.δ (leftEdgeFace (n + 1) q.castSucc (Fin.last 1)) ≫
        (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).rightHom =
      SimplexCategory.δ (leftEdgeFace (n + 1) q.succ 0) ≫
        (leftEdgeIndex (n + 1) q.succ 0).rightHom := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext x
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, ShihIndex.rightHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [leftEdgeFace_last, leftEdgeFace_zero]
  simp only [leftEdgeIndex_gap]
  have hq := q.isLt
  let g := n - q.val
  have hg : 0 < g := by simp only [g]; omega
  have hng : q.val + g = n := by simp only [g]; omega
  simp only [Fin.val_castSucc, Fin.val_succ]
  simp only [show n + 1 - q.val = g + 1 by simp only [g]; omega,
    show n + 1 - (q.val + 1) = g by simp only [g]; omega]
  change
    (if _h : ((Fin.last (n + 2)).succAbove x).val < g + 1 then _ else _) =
      (if _h : ((⟨g, by omega⟩ : Fin (n + 3)).succAbove x).val < g
        then _ else _)
  by_cases hx : x.val < g
  · have hlast : x.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last x
    have hzero : x.castSucc < (⟨g, by omega⟩ : Fin (n + 3)) := hx
    rw [Fin.succAbove_of_castSucc_lt _ _ hlast,
      Fin.succAbove_of_castSucc_lt _ _ hzero]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left (by omega), dite_eq_left hx]
  · have hxg : g ≤ x.val := le_of_not_gt hx
    have hlast : x.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last x
    have hzero : (⟨g, by omega⟩ : Fin (n + 3)) ≤ x.castSucc := hxg
    rw [Fin.succAbove_of_castSucc_lt _ _ hlast,
      Fin.succAbove_of_le_castSucc _ _ hzero]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hxeq : x.val = g
    · rw [dite_eq_left (by omega), dite_eq_right (by omega)]
      apply Fin.ext
      let z : Fin (0 + (q.val + 1) + 1) := ⟨0, by omega⟩
      have hsuffixZero :
          (leftEdgeIndex (n + 1) q.succ 0).gap ≤ x.succ.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_succ]
        omega
      have hinput :
          (leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
              (Fin.cast (by omega) z) := by
        apply Fin.ext
        change x.val + 1 - (leftEdgeIndex (n + 1) q.succ 0).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_zero,
          Fin.zero_succAbove]
        simp only [Fin.val_succ, Fin.val_cast, z]
        omega
      have hshuffle := Shuffle.rightHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle (q.val + 1)) (0 : Fin 2) z
      have hval := congrArg Fin.val hshuffle
      have hmapVal :
          ((leftEdgeIndex (n + 1) q.succ 0).shuffle.rightHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero)).val = 0 := by
        change
          ((Shuffle.leftBoundaryShuffle
              (Shuffle.leftUnitShuffle (q.val + 1)) 0).rightHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput
              x.succ hsuffixZero)).val = 0
        calc
          _ = ((Shuffle.leftBoundaryShuffle
                (Shuffle.leftUnitShuffle (q.val + 1)) 0).rightHom.toOrderHom
              ((Shuffle.leftBoundaryIndex
                  (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
                (Fin.cast (by omega) z))).val := by rw [hinput]
          _ = ((Shuffle.leftUnitShuffle (q.val + 1)).rightHom.toOrderHom z).val := hval
          _ = 0 := by
            simp [Shuffle.leftUnitShuffle_rightHom, z]
      change x.val = g + _ + _
      rw [hmapVal]
      simp only [leftEdgeIndex]
      omega
    · rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      apply Fin.ext
      let zLast : Fin (0 + q.val + 1) := ⟨x.val - (g + 1), by
        have hxlt := x.isLt
        change x.val < n + 2 at hxlt
        omega⟩
      let zZero : Fin (0 + (q.val + 1) + 1) := ⟨x.val - g, by
        have hxlt := x.isLt
        change x.val < n + 2 at hxlt
        omega⟩
      have hsuffixLast :
          (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).gap ≤
            x.castSucc.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_castSucc]
        omega
      have hsuffixZero :
          (leftEdgeIndex (n + 1) q.succ 0).gap ≤ x.succ.val := by
        rw [leftEdgeIndex_gap]
        simp only [Fin.val_succ]
        omega
      have hinputLast :
          (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
              x.castSucc hsuffixLast =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q.val)
              (Fin.last 1)).succAbove (Fin.cast (by omega) zLast) := by
        apply Fin.ext
        change x.val - (leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_last,
          Fin.succAbove_last]
        simp only [Fin.val_castSucc, Fin.val_cast, zLast]
        omega
      have hinputZero :
          (leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero =
            (Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
              (Fin.cast (by omega) zZero) := by
        apply Fin.ext
        change x.val + 1 - (leftEdgeIndex (n + 1) q.succ 0).gap = _
        rw [leftEdgeIndex_gap, Shuffle.leftBoundaryIndex_zero,
          Fin.zero_succAbove]
        simp only [Fin.val_succ, Fin.val_cast, zZero]
        omega
      have hshuffleLast := Shuffle.rightHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle q.val) (Fin.last 1) zLast
      have hshuffleZero := Shuffle.rightHom_leftBoundaryShuffle_succAbove
        (Shuffle.leftUnitShuffle (q.val + 1)) (0 : Fin 2) zZero
      have hvalLast := congrArg Fin.val hshuffleLast
      have hvalZero := congrArg Fin.val hshuffleZero
      have hmapLast :
          ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).shuffle.rightHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
              x.castSucc hsuffixLast)).val = zLast.val := by
        change ((Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
            (Fin.last 1)).rightHom.toOrderHom
          ((leftEdgeIndex (n + 1) q.castSucc (Fin.last 1)).suffixInput
            x.castSucc hsuffixLast)).val = zLast.val
        calc
          _ = ((Shuffle.leftBoundaryShuffle (Shuffle.leftUnitShuffle q.val)
                (Fin.last 1)).rightHom.toOrderHom
              ((Shuffle.leftBoundaryIndex (Shuffle.leftUnitShuffle q.val)
                (Fin.last 1)).succAbove (Fin.cast (by omega) zLast))).val := by
            rw [hinputLast]
          _ = ((Shuffle.leftUnitShuffle q.val).rightHom.toOrderHom zLast).val := hvalLast
          _ = zLast.val := by
            simp [Shuffle.leftUnitShuffle_rightHom]
      have hmapZero :
          ((leftEdgeIndex (n + 1) q.succ 0).shuffle.rightHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput x.succ hsuffixZero)).val = zZero.val := by
        change
          ((Shuffle.leftBoundaryShuffle
              (Shuffle.leftUnitShuffle (q.val + 1)) 0).rightHom.toOrderHom
            ((leftEdgeIndex (n + 1) q.succ 0).suffixInput
              x.succ hsuffixZero)).val = zZero.val
        calc
          _ = ((Shuffle.leftBoundaryShuffle
                (Shuffle.leftUnitShuffle (q.val + 1)) 0).rightHom.toOrderHom
              ((Shuffle.leftBoundaryIndex
                  (Shuffle.leftUnitShuffle (q.val + 1)) 0).succAbove
                (Fin.cast (by omega) zZero))).val := by rw [hinputZero]
          _ = ((Shuffle.leftUnitShuffle (q.val + 1)).rightHom.toOrderHom zZero).val := hvalZero
          _ = zZero.val := by
            simp [Shuffle.leftUnitShuffle_rightHom]
      change g + 1 + _ + _ = g + _ + _
      rw [hmapLast, hmapZero]
      simp only [leftEdgeIndex]
      simp only [zLast, zZero]
      omega

end AlgebraicTopology.EilenbergZilber.ShihIndex
