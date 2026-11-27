/-
Copyright (c) 2026 @toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.NativeRelativeCellColimits

/-! # Whole original predecessor, endpoint, lower comparison and empty-native owner -/

@[expose] public section

noncomputable section

universe w t v u

namespace MathlibExtTest.CategoryTheory.SmallObject.NativeRelativeCellColimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits HomotopicalAlgebra
open _root_.CategoryTheory.SmallObject _root_.CategoryTheory.SmallObject.NativeRelativeCells

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : Type t} {s : α → Arrow C} {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : J) (i : α) => (s i).hom) f)
  [HasPushouts C]

/-- Every original native stage has its constructed earlier-cell colimit UP. -/
def allOriginalStageUPs (j : J) : IsColimit (stageCocone c j) := stageIsColimit c j

theorem allOriginalStageDescFactors (j : J)
    (q : Cocone (LowerSetColimits.restriction (diagram c) (before c j))) (a : before c j) :
    (stageCocone c j).ι.app a ≫ (stageIsColimit c j).desc q = q.ι.app a :=
  (stageIsColimit c j).fac q a

theorem allOriginalStageDescUnique (j : J)
    (q : Cocone (LowerSetColimits.restriction (diagram c) (before c j)))
    (m : stageObj c j ⟶ q.pt)
    (hm : ∀ a, (stageCocone c j).ι.app a ≫ m = q.ι.app a) :
    m = (stageIsColimit c j).desc q := (stageIsColimit c j).uniq q m hm

/-- The literal original endpoint has the constructed entire cell-diagram UP. -/
def allOriginalEndpointUP : IsColimit (endpointCocone c) := endpointIsColimit c

theorem allOriginalEndpointFactors (q : Cocone (diagram c)) (a : c.Cells) :
    vertexIncl c a ≫ endpointDesc c q = q.ι.app a := endpointDesc_fac c q a

theorem completeOriginalEndpointUniqueness (q : Cocone (diagram c))
    (m : Under.mk f ⟶ q.pt) (hm : ∀ a, vertexIncl c a ≫ m = q.ι.app a) :
    m = endpointDesc c q := (endpointIsColimit c).uniq q m hm

theorem allOriginalPredecessors (a : c.Cells) :
    (tree c).predecessorObj a = stageObj c a.j := rfl

theorem allOriginalPredecessorMaps (a : c.Cells) :
    (tree c).predecessorMap a = stageToVertex c a := predecessorMap_eq c a

theorem completeOriginalLabelFunction :
    (tree c).label = (fun a : c.Cells => a.i) := rfl

theorem completeOriginalAttachingFunction :
    (tree c).attaching = (fun a : c.Cells => nativeAttaching c a) := rfl

theorem completeOriginalCellFunction :
    (tree c).cell = (fun a : c.Cells => vertexCell c a) := rfl

theorem originalTreeEndpoint : (tree c).endpointObj = Under.mk f := rfl

theorem originalTreeArrow : (tree c).hom = f := rfl

theorem everyOriginalCellEndpoint (a : c.Cells) :
    (tree c).cell a ≫ ((tree c).inclusion a).right = a.ι := vertexCell_incl c a

theorem presentationOriginalSource : (presentation c).arrowIso.hom.left = 𝟙 X := rfl

theorem presentationOriginalTarget : (presentation c).arrowIso.hom.right = 𝟙 Y := rfl

section AllLower

variable [HasColimitsOfSize.{w, w} C]

/-- The actual selected lower predecessor compares to its original native stage. -/
def actualOriginalPredecessorIso (a : c.Cells) :
    (allLowerData c).obj (LowerSet.Iio a) ≅ stageObj c a.j :=
  (tree c).predecessorIso (allLowerData c) a

theorem originalPredecessorIsoLegs (a : c.Cells) (b : LowerSet.Iio a) :
    (allLowerData c).ι (LowerSet.Iio a) b ≫ (actualOriginalPredecessorIso c a).hom =
      (stageCocone c a.j).ι.app b :=
  (tree c).ι_predecessorIso_hom (allLowerData c) a b

/-- The actual selected whole lower colimit compares to the original endpoint. -/
def actualOriginalEndpointIso : (allLowerData c).obj ⊤ ≅ Under.mk f :=
  (tree c).endpointIso (allLowerData c)

theorem originalEndpointIsoLegs (a : c.Cells) :
    (allLowerData c).ι ⊤ ⟨a, by simp⟩ ≫ (actualOriginalEndpointIso c).hom =
      vertexIncl c a := (tree c).ι_endpointIso_hom (allLowerData c) a

/-- Every original lower carrier has its actual constructed ambient colimit UP. -/
def allOriginalLowerUPs (B : LowerSet c.Cells) :
    IsColimit ((allLowerData c).cocone B) := (allLowerData c).isColimit B

theorem allOriginalLowerRootEquations {B D : LowerSet c.Cells} (h : B ≤ D) :
    ((allLowerData c).obj B).hom ≫ ((allLowerData c).map h).right =
      ((allLowerData c).obj D).hom := Under.w ((allLowerData c).map h)

theorem allOriginalLowerFunctorIdentity (B : LowerSet c.Cells) :
    (allLowerFunctor c).map (𝟙 B) = 𝟙 ((allLowerData c).obj B) :=
  (allLowerFunctor c).map_id B

theorem allOriginalLowerFunctorComposition {B D E : LowerSet c.Cells}
    (h : B ⟶ D) (k : D ⟶ E) :
    (allLowerFunctor c).map (h ≫ k) = (allLowerFunctor c).map h ≫ (allLowerFunctor c).map k :=
  (allLowerFunctor c).map_comp h k

end AllLower

section EmptyNative

variable (s : α → Arrow C) (X : C)

/-- A genuine native identity complex has no outgoing attachment step. -/
def identityComplex : RelativeCellComplex.{0}
    (fun (_ : Fin 1) (i : α) => (s i).hom) (𝟙 X) where
  toTransfiniteCompositionOfShape := .ofComposableArrows (.mk₀ X)
  attachCells j hj := False.elim (hj (by
    intro k _
    exact le_of_eq (Subsingleton.elim _ _)))

omit [HasPushouts C] in
theorem identityComplexCellsEmpty : IsEmpty (identityComplex s X).Cells := by
  refine ⟨fun a => a.hj ?_⟩
  intro k _
  exact le_of_eq (Subsingleton.elim _ _)

theorem identityComplexOriginalRoot : (tree (identityComplex s X)).hom = 𝟙 X := rfl

theorem identityComplexOriginalEndpoint :
    (tree (identityComplex s X)).endpointObj = Under.mk (𝟙 X) := rfl

/-- The actual empty native identity complex retains its entire endpoint UP. -/
def identityComplexWholeUP : IsColimit (endpointCocone (identityComplex s X)) :=
  endpointIsColimit (identityComplex s X)

end EmptyNative

end MathlibExtTest.CategoryTheory.SmallObject.NativeRelativeCellColimits
