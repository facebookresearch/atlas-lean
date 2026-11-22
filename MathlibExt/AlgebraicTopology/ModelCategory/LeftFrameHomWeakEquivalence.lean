/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightFrameHomBoundary
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite
public import Mathlib.CategoryTheory.Limits.Opposites
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries

/-!
# The original left frame Hom in the ordinary opposite model category

Opposing a cosimplicial object turns its actual latching colimit into the
actual full matching limit of its opposite simplicial object.  The indexing
equivalence retains all original proper arrows and triangles.  The canonical
matching map is identified with the opposite of the original latching map.

The ordinary opposite model structure therefore supplies matching fibrations
from original latching cofibrations.  The full-boundary Brown law for right Hom
then gives weak preservation in the target of the original left frame Hom.
No cofibrant generation in the opposite category is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.LeftFrameHomWeakEquivalence

variable {C : Type u} [Category.{v} C]

section Boundary

variable [HasFiniteColimits C]

/-- The opposite latching colimit with all original matching projections. -/
@[implicit_reducible]
def oppositeLatchingCone (A : CosimplicialObject C) (j : SimplexCategory) :
    Cone (SimplexCategory.reedyOp.matchingDiagram A.op (op j)) :=
  (Cone.postcompose
    (ReedyStructure.BoundaryOpposite.diagramIso SimplexCategory.reedy A j).inv).obj
      ((colimit.cocone (SimplexCategory.reedy.latchingDiagram A j)).op.whisker
        (ReedyStructure.BoundaryOpposite.equivalence SimplexCategory.reedy j).functor)

/-- The actual universal latching colimit gives the whole opposite matching limit. -/
def oppositeLatchingIsLimit (A : CosimplicialObject C) (j : SimplexCategory) :
    IsLimit (oppositeLatchingCone A j) :=
  (IsLimit.postcomposeInvEquiv
    (ReedyStructure.BoundaryOpposite.diagramIso SimplexCategory.reedy A j) _).symm
      ((colimit.isColimit (SimplexCategory.reedy.latchingDiagram A j)).op.whiskerEquivalence
        (ReedyStructure.BoundaryOpposite.equivalence SimplexCategory.reedy j))

/-- The transported cone retains the same original opposite latching projection. -/
theorem oppositeLatchingCone_π (A : CosimplicialObject C) (j : SimplexCategory)
    (a : SimplexCategory.reedyOp.Matching (op j)) :
    (oppositeLatchingCone A j).π.app a =
      (colimit.ι (SimplexCategory.reedy.latchingDiagram A j)
        (ReedyStructure.BoundaryOpposite.matchingToLatchingObj SimplexCategory.reedy j a)).op := by
  change (colimit.ι (SimplexCategory.reedy.latchingDiagram A j)
    (ReedyStructure.BoundaryOpposite.matchingToLatchingObj SimplexCategory.reedy j a)).op ≫
      𝟙 _ = _
  exact Category.comp_id _

/-- The canonical matching limit is the opposite of the original latching colimit. -/
def oppositeMatchingIso (A : CosimplicialObject C) (j : SimplexCategory) :
    limit (SimplexCategory.reedyOp.matchingDiagram A.op (op j)) ≅
      op (colimit (SimplexCategory.reedy.latchingDiagram A j)) :=
  limit.isoLimitCone ⟨oppositeLatchingCone A j, oppositeLatchingIsLimit A j⟩

/-- The canonical isomorphism retains every original matching projection. -/
@[reassoc]
theorem oppositeMatchingIso_hom_π (A : CosimplicialObject C) (j : SimplexCategory)
    (a : SimplexCategory.reedyOp.Matching (op j)) :
    (oppositeMatchingIso A j).hom ≫
      (colimit.ι (SimplexCategory.reedy.latchingDiagram A j)
        (ReedyStructure.BoundaryOpposite.matchingToLatchingObj SimplexCategory.reedy j a)).op =
      limit.π (SimplexCategory.reedyOp.matchingDiagram A.op (op j)) a := by
  rw [← oppositeLatchingCone_π]
  exact limit.isoLimitCone_hom_π ⟨oppositeLatchingCone A j, oppositeLatchingIsLimit A j⟩ a

set_option backward.isDefEq.respectTransparency false in
/-- The entire opposite matching arrow is the original latching arrow with its direction reversed. -/
theorem matchingMap_oppositeMatchingIso (A : CosimplicialObject C) (j : SimplexCategory) :
    ReedyStructure.matchingMap SimplexCategory.reedyOp A.op (op j) ≫
      (oppositeMatchingIso A j).hom =
        (ReedyStructure.latchingMap SimplexCategory.reedy A j).op := by
  apply (oppositeLatchingIsLimit A j).hom_ext
  intro a
  rw [oppositeLatchingCone_π, Category.assoc, oppositeMatchingIso_hom_π,
    ReedyStructure.matchingMap_π]
  apply Quiver.Hom.unop_inj
  exact (ReedyStructure.latchingMap_ι SimplexCategory.reedy A j
    (ReedyStructure.BoundaryOpposite.matchingToLatchingObj SimplexCategory.reedy j a)).symm

end Boundary

section Algebraic

/-- The original Hom arrow, opposed degree by degree, gives the complete left/right isomorphism. -/
def leftRightOppositeIso (A : CosimplicialObject C) (Y : C) :
    ResolutionHomComplex.left A Y ≅ ResolutionHomComplex.right (op Y) A.op :=
  NatIso.ofComponents
    (fun n =>
      { hom := ↾fun f => f.op
        inv := ↾fun f => f.unop
        hom_inv_id := by ext f; rfl
        inv_hom_id := by ext f; rfl })
    (by
      intro n m g
      ext f
      change A.obj n.unop ⟶ Y at f
      change (A.map g.unop ≫ f ≫ 𝟙 Y).op =
        𝟙 (op Y) ≫ f.op ≫ (A.map g.unop).op
      simp)

/-- The forward identification uses the exact original arrow, with its direction opposed. -/
@[simp]
theorem leftRightOppositeIso_hom_app (A : CosimplicialObject C) (Y : C)
    (n : SimplexCategoryᵒᵖ) (f : A.obj n.unop ⟶ Y) :
    (leftRightOppositeIso A Y).hom.app n f = f.op := rfl

/-- The inverse identification returns the exact same original arrow. -/
@[simp]
theorem leftRightOppositeIso_inv_app (A : CosimplicialObject C) (Y : C)
    (n : SimplexCategoryᵒᵖ) (f : op Y ⟶ A.op.obj n) :
    (leftRightOppositeIso A Y).inv.app n f = f.unop := rfl

/-- Every original target map retains the full postcomposition/precomposition square. -/
theorem leftRightOppositeIso_target (A : CosimplicialObject C) {Y Y' : C} (p : Y ⟶ Y') :
    ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p) ≫
      (leftRightOppositeIso A Y').hom =
    (leftRightOppositeIso A Y).hom ≫ RightFrameHomBoundary.precomp p.op A.op := by
  ext n f
  rfl

/-- Every original cosimplicial source map retains the entire opposite-diagram square. -/
theorem leftRightOppositeIso_source {A A' : CosimplicialObject C} (a : A ⟶ A') (Y : C) :
    ResolutionHomComplex.precomp a ((SimplicialObject.const C).obj Y) ≫
      (leftRightOppositeIso A Y).hom =
    (leftRightOppositeIso A' Y).hom ≫
      ResolutionHomComplex.postcomp ((CosimplicialObject.const Cᵒᵖ).obj (op Y))
        (NatTrans.op a) := by
  ext n f
  rfl

end Algebraic

section Model

variable [ModelCategory C]

/-- Original latching cofibrations give actual matching fibrations in the ordinary opposite model. -/
theorem opposite_matching_fibration (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j)) :
    ∀ j, fibrations Cᵒᵖ (ReedyStructure.matchingMap SimplexCategory.reedyOp A.op j) := by
  intro j
  have hp : fibrations Cᵒᵖ
      (ReedyStructure.latchingMap SimplexCategory.reedy A j.unop).op := by
    rw [fibrations_op]
    exact hA j.unop
  have heq := matchingMap_oppositeMatchingIso A j.unop
  have hcomp : fibrations Cᵒᵖ
      (ReedyStructure.matchingMap SimplexCategory.reedyOp A.op j ≫
        (oppositeMatchingIso A j.unop).hom) := heq.symm ▸ hp
  exact ((fibrations Cᵒᵖ).cancel_right_of_respectsIso _ _).mp hcomp

/-- Every degree of the actual original left frame is cofibrant from its latching cofibrations. -/
theorem coefficient_isCofibrant (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (j : SimplexCategory) : IsCofibrant (A.obj j) := by
  have h : IsFibrant (A.op.obj (op j)) :=
    RightFrameHornGeometry.degree_isFibrant A.op (opposite_matching_fibration A hA) (op j)
  have hf := (isFibrant_iff_of_isTerminal (initial.to (A.obj j)).op initialIsInitial.op).mp h
  rw [fibration_op_iff] at hf
  exact hf

private theorem isCofibrant_op_of_isFibrant (Y : C) [IsFibrant Y] : IsCofibrant (op Y) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from Y).op terminalIsTerminal.op).2
  rw [cofibration_op_iff]
  infer_instance

/-- Original trivial fibrations give trivial Kan fibrations of the same whole left-Hom target map. -/
theorem postcomp_trivialFibration (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    {Y Y' : C} (p : Y ⟶ Y') [Fibration p] [WeakEquivalence p] :
    trivialFibrations SSet.{v}
      (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p)) := by
  have hr := RightFrameHomBoundary.precomp_trivialFibration p.op A.op
    (opposite_matching_fibration A hA)
  exact ((trivialFibrations SSet.{v}).arrow_mk_iso_iff
    (Arrow.isoMk (leftRightOppositeIso A Y) (leftRightOppositeIso A Y')
      (leftRightOppositeIso_target A p).symm)).mpr hr

/-- Brown's ordinary opposite factorization preserves the whole original left-Hom target map. -/
theorem postcomp_weak (A : CosimplicialObject C)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    {Y Y' : C} (p : Y ⟶ Y') [WeakEquivalence p] [IsFibrant Y] [IsFibrant Y'] :
    WeakEquivalence (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p)) := by
  let _ : IsCofibrant (op Y) := isCofibrant_op_of_isFibrant Y
  let _ : IsCofibrant (op Y') := isCofibrant_op_of_isFibrant Y'
  have hr : WeakEquivalence (RightFrameHomBoundary.precomp p.op A.op) :=
    RightFrameHomBoundary.precomp_weak p.op A.op (opposite_matching_fibration A hA)
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk (leftRightOppositeIso A Y) (leftRightOppositeIso A Y')
        (leftRightOppositeIso_target A p).symm)).mpr ((weakEquivalence_iff _).mp hr))

end Model

end HomotopicalAlgebra.LeftFrameHomWeakEquivalence
