/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImages

/-!
# Natural inverse-image functors on actual Deligne--Faltings structures

Objects are the already specified native inverse-image structures, and
morphism maps are fixed by their action on all adjunction-unit generators.
The ordinary functor is implemented from this actual object/map data and
its identity/composition laws. Source: Borne--Vistoli arXiv:1001.0466v2,
Proposition3.9 and Remark3.11. No root/parabolic conclusion is an input.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImages
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
universe u

/-- A canonical implementation datum, pinned to native inverse images and
all local generator morphisms; not an unconstrained functor on categories. -/
structure InverseImageFunctor {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f]
    (A : DeligneFaltingsSheaves.MonoidSheaf X) where
  object : ∀ D : Structure A, PullbackData D f
  map : ∀ {D E : Structure A}, (D ⟶ E) → ((object D).pulled ⟶ (object E).pulled)
  map_id : ∀ D, map (𝟙 D) = 𝟙 ((object D).pulled)
  map_comp : ∀ {D E F : Structure A} (a : D ⟶ E) (b : E ⟶ F), map (a ≫ b) = map a ≫ map b
  normalization : ∀ {D E : Structure A} (h : D ⟶ E) (U : X.Etale) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback (projection f U)).map (h.comparison U a).hom ≫
      ((object E).comparison U a).hom =
    ((object D).comparison U a).hom ≫
      ((map h).comparison ((etaleBaseChange f).obj U) (generator f A U a)).hom

/-- The actual functor from the normalized object/map implementation. -/
def InverseImageFunctor.functor {X T : Scheme.{u}} {f : T ⟶ X} [HasInverseImage f]
    {A : DeligneFaltingsSheaves.MonoidSheaf X} (P : InverseImageFunctor f A) :
    Structure A ⥤ Structure ((monoidPullback f).obj A) where
  obj D := (P.object D).pulled
  map h := P.map h
  map_id := P.map_id
  map_comp := P.map_comp

end MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
