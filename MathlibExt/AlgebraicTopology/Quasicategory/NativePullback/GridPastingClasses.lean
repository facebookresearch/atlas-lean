/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.GridPasting
import MathlibExt.AlgebraicTopology.Quasicategory.WideSubcategory.Basic

/-!
# Original ambigressive classes under coherent grid pasting

Ingressive and egressive membership classifies the original edges in the
native homotopy category. The entire original coherent grid stays in X.
The two actual row triangles prove composition of the outer horizontal
legs; the original outer vertical legs are unchanged.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.NativePullback

/-- The source's ambigressive condition on the four original square legs.
The original square and all its higher cells are retained. -/
def IsAmbigressiveSquare {X : SSet.{u}}
    (P Q : MorphismProperty (hoFunctor.obj X)) (q : squareShape.{u} ⟶ X) : Prop :=
  P (Edge.mk' (yonedaEquiv (topEdge ≫ q))).toHoHom ∧
  P (Edge.mk' (yonedaEquiv (bottomEdge ≫ q))).toHoHom ∧
  Q (Edge.mk' (yonedaEquiv (leftEdge ≫ q))).toHoHom ∧
  Q (Edge.mk' (yonedaEquiv (rightEdge ≫ q))).toHoHom

private theorem triangle_long_property {X : SSet.{u}}
    (P : MorphismProperty (hoFunctor.obj X)) [P.IsStableUnderComposition]
    (t : (Δ[2] : SSet.{u}) ⟶ X)
    (h₂ : P (Edge.mk' (X.δ (2 : Fin 3) (yonedaEquiv t))).toHoHom)
    (h₀ : P (Edge.mk' (X.δ (0 : Fin 3) (yonedaEquiv t))).toHoHom) :
    P (Edge.mk' (X.δ (1 : Fin 3) (yonedaEquiv t))).toHoHom := by
  obtain ⟨a, b, c, e₀₁, e₁₂, e₀₂, h, hs⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv t)
  have h01 : e₀₁.edge = X.δ 2 (yonedaEquiv t) := h.d₂.symm.trans (by rw [hs])
  have h12 : e₁₂.edge = X.δ 0 (yonedaEquiv t) := h.d₀.symm.trans (by rw [hs])
  have h02 : e₀₂.edge = X.δ 1 (yonedaEquiv t) := h.d₁.symm.trans (by rw [hs])
  have hp01 : P e₀₁.toHoHom := (Edge.morphismProperty_iff_of_edge_eq P h01).mpr h₂
  have hp12 : P e₁₂.toHoHom := (Edge.morphismProperty_iff_of_edge_eq P h12).mpr h₀
  have hp02 : P e₀₂.toHoHom := by
    rw [← Edge.toHoHom_comp h]
    exact P.comp_mem _ _ hp01 hp12
  exact (Edge.morphismProperty_iff_of_edge_eq P h02).mp hp02

/-- The entire original upper row composition triangle00→10→20. -/
def gridUpperRow : (Δ[2] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (⟨(0, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(1, 0)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(1, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(2, 0)⟩ from ⟨by decide, le_rfl⟩)))
/-- The entire original lower row composition triangle01→11→21. -/
def gridLowerRow : (Δ[2] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  gridBottomTriangle ≫ pastingBaseInclusion ≫ pastingConeInclusion

private theorem upper_left : stdSimplex.δ (2 : Fin 3) ≫ gridUpperRow.{u} = topEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem upper_right : stdSimplex.δ (0 : Fin 3) ≫ gridUpperRow.{u} =
    topEdge ≫ pastingRightSquare ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem upper_outer : stdSimplex.δ (1 : Fin 3) ≫ gridUpperRow.{u} = topEdge ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem lower_left : stdSimplex.δ (2 : Fin 3) ≫ gridLowerRow.{u} = bottomEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem lower_right : stdSimplex.δ (0 : Fin 3) ≫ gridLowerRow.{u} =
    bottomEdge ≫ pastingRightSquare ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem lower_outer : stdSimplex.δ (1 : Fin 3) ≫ gridLowerRow.{u} = bottomEdge ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original outer left vertical leg is the same original column-zero edge. -/
theorem gridOuter_leftEdge : leftEdge.{u} ≫ gridOuterSquare = leftEdge ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
/-- The original outer right vertical leg is the same original column-two edge. -/
theorem gridOuter_rightEdge : rightEdge.{u} ≫ gridOuterSquare =
    rightEdge ≫ pastingRightSquare ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The two original ambigressive squares have an original ambigressive outer square.
Only class closure on the actual upper/lower row compositions is used. -/
theorem isAmbigressiveSquare_grid_outer {X : SSet.{u}}
    (P Q : MorphismProperty (hoFunctor.obj X)) [P.IsStableUnderComposition]
    (q : pastingGridShape.{u} ⟶ X)
    (hL : IsAmbigressiveSquare P Q (gridLeftSquare ≫ q))
    (hR : IsAmbigressiveSquare P Q (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    IsAmbigressiveSquare P Q (gridOuterSquare ≫ q) := by
  have hUpper₂ : P (Edge.mk' (X.δ 2 (yonedaEquiv (gridUpperRow ≫ q)))).toHoHom := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, upper_left, Category.assoc]
    exact hL.1
  have hUpper₀ : P (Edge.mk' (X.δ 0 (yonedaEquiv (gridUpperRow ≫ q)))).toHoHom := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, upper_right, Category.assoc]
    exact hR.1
  have hLower₂ : P (Edge.mk' (X.δ 2 (yonedaEquiv (gridLowerRow ≫ q)))).toHoHom := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, lower_left, Category.assoc]
    exact hL.2.1
  have hLower₀ : P (Edge.mk' (X.δ 0 (yonedaEquiv (gridLowerRow ≫ q)))).toHoHom := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, lower_right, Category.assoc]
    exact hR.2.1
  have hU := triangle_long_property P (gridUpperRow ≫ q) hUpper₂ hUpper₀
  have hD := triangle_long_property P (gridLowerRow ≫ q) hLower₂ hLower₀
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, upper_outer, Category.assoc] at hU
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, lower_outer, Category.assoc] at hD
  refine ⟨hU, hD, ?_, ?_⟩
  · rw [← Category.assoc, gridOuter_leftEdge, Category.assoc]
    exact hL.2.2.1
  · rw [← Category.assoc, gridOuter_rightEdge, Category.assoc]
    exact hR.2.2.2

/-- The source's actual ambigressive pullback pasting keeps the whole original grid
and original ingressive/egressive legs. -/
theorem ambigressivePullback_grid_paste {X : SSet.{u}} [Quasicategory X]
    (P Q : MorphismProperty (hoFunctor.obj X)) [P.IsStableUnderComposition]
    (q : pastingGridShape.{u} ⟶ X)
    (hL : IsAmbigressiveSquare P Q (gridLeftSquare ≫ q))
    (hR : IsAmbigressiveSquare P Q (pastingRightSquare ≫ pastingConeInclusion ≫ q))
    (hpL : IsPullbackSquare (gridLeftSquare ≫ q))
    (hpR : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    IsAmbigressiveSquare P Q (gridOuterSquare ≫ q) ∧ IsPullbackSquare (gridOuterSquare ≫ q) :=
  ⟨isAmbigressiveSquare_grid_outer P Q q hL hR, isPullbackSquare_grid_paste q hpL hpR⟩

/-- Coordinate transposition exchanges exactly the original two leg classes. -/
theorem isAmbigressiveSquare_swap {X : SSet.{u}}
    (P Q : MorphismProperty (hoFunctor.obj X)) (q : squareShape.{u} ⟶ X) :
    IsAmbigressiveSquare Q P (squareSwapIso.hom ≫ q) ↔ IsAmbigressiveSquare P Q q := by
  have ht : topEdge ≫ (squareSwapIso.hom ≫ q) = leftEdge ≫ q := by
    rw [← Category.assoc, topEdge_swap]
  have hb : bottomEdge ≫ (squareSwapIso.hom ≫ q) = rightEdge ≫ q := by
    rw [← Category.assoc, bottomEdge_swap]
  have hl : leftEdge ≫ (squareSwapIso.hom ≫ q) = topEdge ≫ q := by
    rw [← Category.assoc, leftEdge_swap]
  have hr : rightEdge ≫ (squareSwapIso.hom ≫ q) = bottomEdge ≫ q := by
    rw [← Category.assoc, rightEdge_swap]
  have hT := congrArg (fun e : (Δ[1] : SSet.{u}) ⟶ X => Q (Edge.mk' (yonedaEquiv e)).toHoHom) ht
  have hB := congrArg (fun e : (Δ[1] : SSet.{u}) ⟶ X => Q (Edge.mk' (yonedaEquiv e)).toHoHom) hb
  have hL := congrArg (fun e : (Δ[1] : SSet.{u}) ⟶ X => P (Edge.mk' (yonedaEquiv e)).toHoHom) hl
  have hR := congrArg (fun e : (Δ[1] : SSet.{u}) ⟶ X => P (Edge.mk' (yonedaEquiv e)).toHoHom) hr
  constructor
  · rintro ⟨hQt, hQb, hPl, hPr⟩
    exact ⟨hL.mp hPl, hR.mp hPr, hT.mp hQt, hB.mp hQb⟩
  · rintro ⟨hPt, hPb, hQl, hQr⟩
    exact ⟨hT.mpr hQl, hB.mpr hQr, hL.mpr hPt, hR.mpr hPb⟩

/-- The original vertical outer square retains both leg classes.
Only egressive composition of the two original vertical row edges is used. -/
theorem isAmbigressiveSquare_vertical_outer {X : SSet.{u}}
    (P Q : MorphismProperty (hoFunctor.obj X)) [Q.IsStableUnderComposition]
    (q : verticalGridShape.{u} ⟶ X)
    (hT : IsAmbigressiveSquare P Q (verticalTopSquare ≫ q))
    (hB : IsAmbigressiveSquare P Q (verticalBottomSquare ≫ q)) :
    IsAmbigressiveSquare P Q (verticalOuterSquare ≫ q) := by
  have hL : IsAmbigressiveSquare Q P (gridLeftSquare ≫ (gridTransposeIso.hom ≫ q)) := by
    rw [← Category.assoc, gridLeftSquare_transpose, Category.assoc]
    exact (isAmbigressiveSquare_swap P Q _).mpr hT
  have hR : IsAmbigressiveSquare Q P
      (pastingRightSquare ≫ pastingConeInclusion ≫ (gridTransposeIso.hom ≫ q)) := by
    have hb : IsAmbigressiveSquare Q P (squareSwapIso.hom ≫ (verticalBottomSquare ≫ q)) :=
      (isAmbigressiveSquare_swap (X := X) P Q (verticalBottomSquare ≫ q)).mpr hB
    have hm : pastingRightSquare ≫ pastingConeInclusion ≫ (gridTransposeIso.hom ≫ q) =
        squareSwapIso.hom ≫ (verticalBottomSquare ≫ q) := by
      calc
        _ = (pastingRightSquare ≫ pastingConeInclusion ≫ gridTransposeIso.hom) ≫ q := by
          simp only [Category.assoc]
        _ = (squareSwapIso.hom ≫ verticalBottomSquare) ≫ q :=
          congrArg (fun i : squareShape.{u} ⟶ verticalGridShape.{u} => i ≫ q) gridRightSquare_transpose
        _ = _ := Category.assoc _ _ _
    exact (congrArg (IsAmbigressiveSquare (X := X) Q P) hm).mpr hb
  have h := isAmbigressiveSquare_grid_outer Q P (gridTransposeIso.hom ≫ q) hL hR
  rw [← Category.assoc, gridOuterSquare_transpose, Category.assoc] at h
  exact (isAmbigressiveSquare_swap P Q _).mp h

/-- Vertical ambigressive pullback pasting retains the entire original
coherent grid and original ingressive/egressive classes. -/
theorem ambigressivePullback_vertical_paste {X : SSet.{u}} [Quasicategory X]
    (P Q : MorphismProperty (hoFunctor.obj X)) [Q.IsStableUnderComposition]
    (q : verticalGridShape.{u} ⟶ X)
    (hT : IsAmbigressiveSquare P Q (verticalTopSquare ≫ q))
    (hB : IsAmbigressiveSquare P Q (verticalBottomSquare ≫ q))
    (hpT : IsPullbackSquare (verticalTopSquare ≫ q))
    (hpB : IsPullbackSquare (verticalBottomSquare ≫ q)) :
    IsAmbigressiveSquare P Q (verticalOuterSquare ≫ q) ∧ IsPullbackSquare (verticalOuterSquare ≫ q) :=
  ⟨isAmbigressiveSquare_vertical_outer P Q q hT hB, isPullbackSquare_vertical_paste q hpT hpB⟩

end SSet.NativePullback
