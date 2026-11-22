/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalSSet
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSpace.ZerothRow

/-!
# The wrapped first-projection and zeroth-row adjunction

Transport the existing raw `p₁* ⊣ i₁*` through the canonical carrier
equivalences. The left functor has bidegree `(m,n)` equal to `A_m`;
the right functor retains `X_(m,0)`. Unit and counit are the original
row-identification and inner-degeneracy maps.

The data are the adjunction used in Joyal–Tierney Theorem 4.11, with its
setup in §4 and Proposition 4.7. Model preservation is a further property.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SimplicialSpace

/-- The first-projection functor on the actual designated carriers. -/
abbrev comparisonLeft : JoyalSSet.{u} ⥤ SimplicialSpace.{u} :=
  (JoyalSSet.forget ⋙ SSet.simplicialSpaceDiscrete) ⋙ ofSimplicialObject

/-- The zeroth-row functor on the actual designated carriers. -/
abbrev comparisonRight : SimplicialSpace.{u} ⥤ JoyalSSet.{u} :=
  forget ⋙ (SSet.Rezk.zerothRow ⋙ JoyalSSet.ofSSet)

/-- Transport of the actual raw first-projection/zeroth-row adjunction. -/
def comparisonAdjunction : comparisonLeft.{u} ⊣ comparisonRight.{u} :=
  (JoyalSSet.equivalenceSSet.toAdjunction.comp SSet.Rezk.zerothRowAdjunction).comp
    equivalenceSimplicialObject.symm.toAdjunction

/-- The left functor retains the first bidegree coordinate. -/
lemma comparisonLeft_obj_obj (A : JoyalSSet.{u}) (m n : SimplexCategoryᵒᵖ) :
    ((comparisonLeft.obj A).diagram.obj m).obj n = A.toSSet.obj m := rfl

/-- A map under the left functor is the original outer simplicial map. -/
lemma comparisonLeft_map_app {A B : JoyalSSet.{u}} (f : A ⟶ B)
    (m n : SimplexCategoryᵒᵖ) :
    (((comparisonLeft.map f).hom.app m).app n) =
      (JoyalSSet.forget.map f).app m := rfl

/-- The right functor retains the inner zeroth component in every outer degree. -/
lemma comparisonRight_obj_obj (X : SimplicialSpace.{u}) (m : SimplexCategoryᵒᵖ) :
    (JoyalSSet.forget.obj (comparisonRight.obj X)).obj m =
      (X.diagram.obj m).obj (op ⦋0⦌) := rfl

/-- A map under the right functor is its original inner-zero component. -/
lemma comparisonRight_map_app {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (m : SimplexCategoryᵒᵖ) :
    (JoyalSSet.forget.map (comparisonRight.map f)).app m =
      (f.hom.app m).app (op ⦋0⦌) := rfl

/-- The unit is the identity under the canonical row identification. -/
lemma comparisonAdjunction_unit_app (A : JoyalSSet.{u}) (m : SimplexCategoryᵒᵖ) :
    (JoyalSSet.forget.map (comparisonAdjunction.unit.app A)).app m =
      𝟙 (A.toSSet.obj m) := rfl

/-- The counit repeats an inner vertex through the unique map `[n] → [0]`. -/
lemma comparisonAdjunction_counit_app (X : SimplicialSpace.{u})
    (m n : SimplexCategoryᵒᵖ) :
    (((comparisonAdjunction.counit.app X).hom.app m).app n) =
      (X.diagram.obj m).map (SimplexCategory.const n.unop ⦋0⦌ 0).op := by
  change ((SSet.Rezk.zerothRowAdjunction.counit.app X.diagram).app m).app n = _
  exact SSet.Rezk.zerothRowAdjunction_counit_app X.diagram m n

end SimplicialSpace
