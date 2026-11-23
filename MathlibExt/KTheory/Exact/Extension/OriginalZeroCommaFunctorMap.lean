/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.StabilizedFunctorTarget
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The actual exact-functor map on the original zero left-comma category

The original stabilized extension functor and its proved Quillen target
square give the comma map. The canonical mapped-zero comparison is used
in its inverse direction, from the selected target zero to the mapped
source zero. Every total object and morphism remains the actual image;
no fiber equivalence, comparison square or desired naturality is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] CategoryTheory.MonoidalActionCategory.diagonalAction

universe uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The actual original zero-comma map induced by F and its canonical mapped-zero Iso. -/
public def zeroStructuredArrowMap :
    StructuredArrow (⟨(0 : C)⟩ : QuillenQ C) (ExtensionCategory.localizedTarget (C := C)) ⥤
      StructuredArrow (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) :=
  StructuredArrow.map₂
    (F := ExtensionCategory.stabilizedFunctorMap F) (G := QuillenQ.map F)
    (QuillenQ.zeroComparisonIso F).inv
    (eqToIso (ExtensionCategory.stabilizedFunctorMap_target F).symm).hom

private theorem originalZeroCommaObjectComputed
    (X : StructuredArrow (⟨(0 : C)⟩ : QuillenQ C)
      (ExtensionCategory.localizedTarget (C := C))) :
    ((zeroStructuredArrowMap F).obj X).right =
      (ExtensionCategory.stabilizedFunctorMap F).obj X.right := rfl

/-- Every comma object retains the literal original total-functor image. -/
public theorem zeroStructuredArrowMap_obj_right
    (X : StructuredArrow (⟨(0 : C)⟩ : QuillenQ C)
      (ExtensionCategory.localizedTarget (C := C))) :
    ((zeroStructuredArrowMap F).obj X).right =
      (ExtensionCategory.stabilizedFunctorMap F).obj X.right :=
  originalZeroCommaObjectComputed F X

private theorem originalZeroCommaArrowComputed
    (X : StructuredArrow (⟨(0 : C)⟩ : QuillenQ C)
      (ExtensionCategory.localizedTarget (C := C))) :
    HEq ((zeroStructuredArrowMap F).obj X).hom
      ((QuillenQ.zeroComparisonIso F).inv ≫ (QuillenQ.map F).map X.hom ≫
        (eqToIso (ExtensionCategory.stabilizedFunctorMap_target F).symm).hom.app X.right) :=
  heq_of_eq rfl

/--
The original comma arrow uses exactly the canonical zero, Quillen map and target-square route.
-/
public theorem zeroStructuredArrowMap_obj_hom_heq
    (X : StructuredArrow (⟨(0 : C)⟩ : QuillenQ C)
      (ExtensionCategory.localizedTarget (C := C))) :
    HEq ((zeroStructuredArrowMap F).obj X).hom
      ((QuillenQ.zeroComparisonIso F).inv ≫ (QuillenQ.map F).map X.hom ≫
        (eqToIso (ExtensionCategory.stabilizedFunctorMap_target F).symm).hom.app X.right) :=
  originalZeroCommaArrowComputed F X

private theorem originalZeroCommaProjectionComputed :
    zeroStructuredArrowMap F ⋙ StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) =
      StructuredArrow.proj (⟨(0 : C)⟩ : QuillenQ C)
        (ExtensionCategory.localizedTarget (C := C)) ⋙ ExtensionCategory.stabilizedFunctorMap F :=
by
  refine Functor.hext (fun _ => rfl) ?_
  intro X Y f
  exact heq_of_eq rfl

/-- The whole comma projection agrees with the actual original total map on all objects/arrows. -/
public theorem zeroStructuredArrowMap_projection :
    zeroStructuredArrowMap F ⋙ StructuredArrow.proj (⟨(0 : D)⟩ : QuillenQ D)
        (ExtensionCategory.localizedTarget (C := D)) =
      StructuredArrow.proj (⟨(0 : C)⟩ : QuillenQ C)
        (ExtensionCategory.localizedTarget (C := C)) ⋙ ExtensionCategory.stabilizedFunctorMap F :=
  originalZeroCommaProjectionComputed F

end AlgebraicKTheory.OriginalQZeroComparison

end
