/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InternalHomAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction

/-!
# Native marked product and internal-Hom parametrized lifting

The existing original marked internal-Hom adjunction is natural in its
whole original source map. It therefore gives a genuine parametrized
adjunction on the actual marked carrier. Native marked pushout-products
transpose to the original marked internal-Hom pullback comparison.
No tensor-model compatibility or model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace SSet.Marked

/-- Original marked products retain both actual marked variables. -/
def markedProductBifunctor : Marked.{u} ⥤ Marked.{u} ⥤ Marked.{u} where
  obj := prodRight
  map := prodRightMap
  map_id X := by
    apply NatTrans.ext
    funext A
    exact prodMap_id A X
  map_comp f g := by
    apply NatTrans.ext
    funext A
    exact (congrArg (fun t => prodMap t (f ≫ g)) (Category.id_comp (𝟙 A))).symm.trans
      (prodMap_comp (𝟙 A) (𝟙 A) f g)

/-- The actual marked internal-Hom is contravariant in its whole source and covariant in its target. -/
def markedInternalHomBifunctor : Marked.{u}ᵒᵖ ⥤ Marked.{u} ⥤ Marked.{u} where
  obj X := internalHomFunctor X.unop
  map f :=
    { app Y := internalHomPre f.unop Y
      naturality Y Y' p := Hom.ext (mappingComplexPre_post .minimal f.unop p).symm }
  map_id X := by
    apply NatTrans.ext
    funext Y
    exact Hom.ext (mappingComplexPre_id .minimal X.unop Y)
  map_comp f g := by
    apply NatTrans.ext
    funext Y
    exact Hom.ext (mappingComplexPre_comp .minimal g.unop f.unop Y)

/-- Native currying retains the same original marked source-product map. -/
theorem curry_source {X X' A Y : Marked.{u}} (f : X ⟶ X') (g : prod A X' ⟶ Y) :
    curry (prodMap (𝟙 A) f ≫ g) = curry g ≫ internalHomPre f Y := by
  apply Hom.ext
  ext n a
  exact Hom.ext rfl

/-- The original marked product/internal-Hom adjunction is genuinely parametrized on both marked variables. -/
def markedProductAdjunction₂ : markedProductBifunctor.{u} ⊣₂ markedInternalHomBifunctor.{u} :=
  ParametrizedAdjunction.mk' internalHomAdjunction (by
    intro X X' f A Y g
    exact curry_source f g)

/-- The actual original marked product pushout for two original marked maps. -/
def markedProductPushout {A D X Y : Marked.{u}} (a : A ⟶ D) (i : X ⟶ Y) :
    markedProductBifunctor.PushoutObjObj a i := Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The native original marked pushout-product retains its exact selected pushout and marks. -/
def markedPushoutProduct {A D X Y : Marked.{u}} (a : A ⟶ D) (i : X ⟶ Y) :
    (markedProductPushout a i).pt ⟶ prod Y D := (markedProductPushout a i).ι

/-- The actual marked internal-Hom pullback for the original parameter and target maps. -/
def markedInternalHomPullback {A D E F : Marked.{u}} (a : A ⟶ D) (p : E ⟶ F) :
    markedInternalHomBifunctor.PullbackObjObj a p := Functor.PullbackObjObj.ofHasPullback _ _ _

/-- The original marked cotensor comparison retains the supplied parameter restriction and target map. -/
def markedInternalHomComparison {A D E F : Marked.{u}} (a : A ⟶ D) (p : E ⟶ F) :
    internalHom D E ⟶ (markedInternalHomPullback a p).pt := (markedInternalHomPullback a p).π

/-- The original whole marked lifting squares transpose exactly through the native marked product adjunction. -/
theorem markedPushoutProduct_hasLiftingProperty_iff {A D X Y E F : Marked.{u}}
    (a : A ⟶ D) (i : X ⟶ Y) (p : E ⟶ F) :
    HasLiftingProperty (markedPushoutProduct a i) p ↔ HasLiftingProperty i (markedInternalHomComparison a p) :=
  markedProductAdjunction₂.hasLiftingProperty_iff (markedProductPushout a i) (markedInternalHomPullback a p)

end SSet.Marked
