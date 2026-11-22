/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Opposite
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.GridPasting
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Original coherent grid pushout pasting

The source is the entire ordinary nerve of the original six-vertex grid.
Its two cell maps and outer-square map are whole original coherent squares.
Reversal of both finite coordinates compares this grid with its opposite.
The earned native opposite theorem and original pullback pasting theorem
then prove pushout pasting and cancellation with every boundary retained.

The square charts order the vertical branch before the horizontal branch.
The literal vertex and row equations below record this convention.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePushout

/-- The same original six-object grid, with its native product preorder. -/
abbrev PastingGridObjects := NativePullback.PastingGridObjects.{u}

/-- The entire original coherent grid nerve, including its three-dimensional cells. -/
abbrev pastingGridShape : SSet.{u} := nerve PastingGridObjects.{u}

/-- Reverse both original finite grid coordinates. -/
def gridReverseFunctor : PastingGridObjects.{u}ᵒᵖ ⥤ PastingGridObjects.{u} where
  obj v := ULift.up (v.unop.down.1.rev, v.unop.down.2.rev)
  map {v w} f := by
    have h : w.unop.down.1 ≤ v.unop.down.1 ∧ w.unop.down.2 ≤ v.unop.down.2 := leOfHom f.unop
    exact homOfLE ⟨Fin.rev_le_rev.mpr h.1, Fin.rev_le_rev.mpr h.2⟩

/-- The inverse reversal keeps the whole original grid category. -/
def gridReverseInverseFunctor : PastingGridObjects.{u} ⥤ PastingGridObjects.{u}ᵒᵖ where
  obj v := op (ULift.up (v.down.1.rev, v.down.2.rev))
  map {v w} f := by
    have h : v.down.1 ≤ w.down.1 ∧ v.down.2 ≤ w.down.2 := leOfHom f
    exact (homOfLE (show (ULift.up (w.down.1.rev, w.down.2.rev) : PastingGridObjects.{u}) ≤
      ULift.up (v.down.1.rev, v.down.2.rev) from
        ⟨Fin.rev_le_rev.mpr h.1, Fin.rev_le_rev.mpr h.2⟩)).op

/-- Both coordinate reversals identify the whole opposite grid nerve with the original grid. -/
def gridOppNerveIso : nerve PastingGridObjects.{u}ᵒᵖ ≅ pastingGridShape.{u} where
  hom := nerveMap gridReverseFunctor
  inv := nerveMap gridReverseInverseFunctor
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change gridReverseInverseFunctor.obj (gridReverseFunctor.obj (s.obj i)) = s.obj i
    cases s.obj i with
    | op v =>
      rcases v with ⟨⟨a, b⟩⟩
      change op (ULift.up (a.rev.rev, b.rev.rev)) = op (ULift.up (a, b))
      rw [Fin.rev_rev, Fin.rev_rev]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext i
    change gridReverseFunctor.obj (gridReverseInverseFunctor.obj (s.obj i)) = s.obj i
    rcases s.obj i with ⟨⟨a, b⟩⟩
    change ULift.up (a.rev.rev, b.rev.rev) = ULift.up (a, b)
    rw [Fin.rev_rev, Fin.rev_rev]

/-- The actual opposite coherent grid is the same full original grid after coordinate reversal. -/
def gridOppositeIso : NativePullback.pastingGridShape.{u}.op ≅ pastingGridShape.{u} :=
  (nerveOppositeSimplicialIso PastingGridObjects.{u}).symm ≪≫ gridOppNerveIso

/-- The full original left cell in columns zero and one. -/
def gridLeftSquare : squareShape.{u} ⟶ pastingGridShape.{u} :=
  NativePullback.oppositeSquare
    (NativePullback.pastingRightSquare ≫ NativePullback.pastingConeInclusion) ≫ gridOppositeIso.hom

/-- The full original right cell in columns one and two. -/
def gridRightSquare : squareShape.{u} ⟶ pastingGridShape.{u} :=
  NativePullback.oppositeSquare NativePullback.gridLeftSquare ≫ gridOppositeIso.hom

/-- The full original outer square in columns zero and two. -/
def gridOuterSquare : squareShape.{u} ⟶ pastingGridShape.{u} :=
  NativePullback.oppositeSquare NativePullback.gridOuterSquare ≫ gridOppositeIso.hom

/-- An actual original grid vertex as a map from the whole standard point. -/
def gridPoint (v : PastingGridObjects.{u}) : (Δ[0] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ v)

/-- The original left-cell chart retains all four original vertices. -/
theorem gridLeftSquare_point (v : DiamondObjects.{u}) :
    point v ≫ gridLeftSquare = gridPoint (match v with
      | .star => ULift.up (1, 1)
      | .of ⟨WalkingSpan.zero⟩ => ULift.up (0, 0)
      | .of ⟨WalkingSpan.left⟩ => ULift.up (0, 1)
      | .of ⟨WalkingSpan.right⟩ => ULift.up (1, 0)) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  cases v with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The original right-cell chart retains all four original vertices. -/
theorem gridRightSquare_point (v : DiamondObjects.{u}) :
    point v ≫ gridRightSquare = gridPoint (match v with
      | .star => ULift.up (2, 1)
      | .of ⟨WalkingSpan.zero⟩ => ULift.up (1, 0)
      | .of ⟨WalkingSpan.left⟩ => ULift.up (1, 1)
      | .of ⟨WalkingSpan.right⟩ => ULift.up (2, 0)) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  cases v with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The original outer-square chart retains its actual source, branches, and terminal vertex. -/
theorem gridOuterSquare_point (v : DiamondObjects.{u}) :
    point v ≫ gridOuterSquare = gridPoint (match v with
      | .star => ULift.up (2, 1)
      | .of ⟨WalkingSpan.zero⟩ => ULift.up (0, 0)
      | .of ⟨WalkingSpan.left⟩ => ULift.up (0, 1)
      | .of ⟨WalkingSpan.right⟩ => ULift.up (2, 0)) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  cases v with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The exact original common edge glues the two whole original cells. -/
theorem grid_sharedEdge : bottomEdge.{u} ≫ gridLeftSquare = topEdge ≫ gridRightSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original whole lower row, with its two composing edges and long edge. -/
def gridLowerRow : (Δ[2] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (ULift.up (0, 0) : PastingGridObjects.{u}) ≤ ULift.up (1, 0) from
      ⟨by decide, le_rfl⟩))
    (homOfLE (show (ULift.up (1, 0) : PastingGridObjects.{u}) ≤ ULift.up (2, 0) from
      ⟨by decide, le_rfl⟩)))

/-- The original whole upper row, with its two composing edges and long edge. -/
def gridUpperRow : (Δ[2] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (ULift.up (0, 1) : PastingGridObjects.{u}) ≤ ULift.up (1, 1) from
      ⟨by decide, le_rfl⟩))
    (homOfLE (show (ULift.up (1, 1) : PastingGridObjects.{u}) ≤ ULift.up (2, 1) from
      ⟨by decide, le_rfl⟩)))

/-- The first lower row edge is the original left cell's horizontal span leg. -/
theorem gridLowerRow_left : stdSimplex.δ (2 : Fin 3) ≫ gridLowerRow.{u} =
    leftEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The second lower row edge is the original right cell's horizontal span leg. -/
theorem gridLowerRow_right : stdSimplex.δ (0 : Fin 3) ≫ gridLowerRow.{u} =
    leftEdge ≫ gridRightSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The lower row's full long edge is the original outer horizontal span leg. -/
theorem gridLowerRow_outer : stdSimplex.δ (1 : Fin 3) ≫ gridLowerRow.{u} =
    leftEdge ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The first upper row edge is the original left cell's horizontal cocone leg. -/
theorem gridUpperRow_left : stdSimplex.δ (2 : Fin 3) ≫ gridUpperRow.{u} =
    rightEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The second upper row edge is the original right cell's horizontal cocone leg. -/
theorem gridUpperRow_right : stdSimplex.δ (0 : Fin 3) ≫ gridUpperRow.{u} =
    rightEdge ≫ gridRightSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The upper row's whole long edge is the original outer horizontal cocone leg. -/
theorem gridUpperRow_outer : stdSimplex.δ (1 : Fin 3) ≫ gridUpperRow.{u} =
    rightEdge ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original left outer vertical leg is unchanged by horizontal pasting. -/
theorem gridOuter_topEdge : topEdge.{u} ≫ gridOuterSquare = topEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original right outer vertical leg is unchanged by horizontal pasting. -/
theorem gridOuter_bottomEdge : bottomEdge.{u} ≫ gridOuterSquare = bottomEdge ≫ gridRightSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

variable {X : SSet.{u}}

/-- The opposite of the given original whole grid in its original opposite ambient set. -/
def oppositeGrid (q : pastingGridShape.{u} ⟶ X) : NativePullback.pastingGridShape.{u} ⟶ X.op :=
  (opEquivalence.unitIso.app NativePullback.pastingGridShape).hom ≫
    opFunctor.map (gridOppositeIso.hom ≫ q)

/-- The whole square restrictions commute with reversal of the whole original grid. -/
theorem oppositeSquare_gridRestriction
    (i : NativePullback.squareShape.{u} ⟶ NativePullback.pastingGridShape.{u})
    (q : pastingGridShape.{u} ⟶ X) :
    oppositeSquare (NativePullback.oppositeSquare i ≫ gridOppositeIso.hom ≫ q) =
      i ≫ oppositeGrid q := by
  rw [oppositeSquare_comp, NativePullback.oppositeSquare_oppositeSquare]
  let uG : NativePullback.pastingGridShape ⟶ NativePullback.pastingGridShape.op.op :=
    (opEquivalence.unitIso.app NativePullback.pastingGridShape).hom
  let p : NativePullback.pastingGridShape.op.op ⟶ X.op :=
    opFunctor.map (gridOppositeIso.hom ≫ q)
  change (i ≫ uG) ≫ p = i ≫ (uG ≫ p)
  exact Category.assoc i uG p

/-- The independently defined pushout condition on each original cell is the
pullback condition on the same reversed original restriction. -/
theorem isPushoutSquare_gridRestriction_iff
    (i : NativePullback.squareShape.{u} ⟶ NativePullback.pastingGridShape.{u})
    (q : pastingGridShape.{u} ⟶ X) :
    IsPushoutSquare (NativePullback.oppositeSquare i ≫ gridOppositeIso.hom ≫ q) ↔
      NativePullback.IsPullbackSquare (i ≫ oppositeGrid q) := by
  rw [isPushoutSquare_iff_isPullbackSquare_opposite, oppositeSquare_gridRestriction]

/-- A pushout left cell makes the original right cell a pushout exactly when
the full original outer square is a pushout. -/
theorem isPushoutSquare_grid_right_iff_outer [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X) (hL : IsPushoutSquare (gridLeftSquare ≫ q)) :
    IsPushoutSquare (gridRightSquare ≫ q) ↔ IsPushoutSquare (gridOuterSquare ≫ q) := by
  let : Quasicategory X.op := quasicategory_op X
  have hR : NativePullback.IsPullbackSquare
      (NativePullback.pastingRightSquare ≫ NativePullback.pastingConeInclusion ≫ oppositeGrid q) :=
    (isPushoutSquare_gridRestriction_iff
      (NativePullback.pastingRightSquare ≫ NativePullback.pastingConeInclusion) q).mp hL
  have h := NativePullback.isPullbackSquare_grid_left_iff_outer (oppositeGrid q) hR
  exact (isPushoutSquare_gridRestriction_iff NativePullback.gridLeftSquare q).trans
    (h.trans (isPushoutSquare_gridRestriction_iff NativePullback.gridOuterSquare q).symm)

/-- Pasting the two actual original pushout cells gives the actual original outer pushout. -/
theorem isPushoutSquare_grid_paste [Quasicategory X] (q : pastingGridShape.{u} ⟶ X)
    (hL : IsPushoutSquare (gridLeftSquare ≫ q)) (hR : IsPushoutSquare (gridRightSquare ≫ q)) :
    IsPushoutSquare (gridOuterSquare ≫ q) :=
  (isPushoutSquare_grid_right_iff_outer q hL).mp hR

/-- Cancelling the original left pushout from the original outer pushout
recovers the original right pushout cell. -/
theorem isPushoutSquare_grid_cancel [Quasicategory X] (q : pastingGridShape.{u} ⟶ X)
    (hL : IsPushoutSquare (gridLeftSquare ≫ q)) (hO : IsPushoutSquare (gridOuterSquare ≫ q)) :
    IsPushoutSquare (gridRightSquare ≫ q) :=
  (isPushoutSquare_grid_right_iff_outer q hL).mpr hO

end SSet.NativePushout
