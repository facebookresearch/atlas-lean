/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.RingScalarExtensionPseudofunctor

/-!
# Clients of the original native scalar-extension pseudofunctor

The categorical arrows, structural natural isomorphisms and mapped original
morphisms remain the existing native programs on associative rings.
-/

@[expose] public section

noncomputable section

open CategoryTheory FGProjectiveCat
open ModuleCat.RingHomScalarExtension
open scoped CategoryTheory.Bicategory

universe u

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

example (f : R →+* S) :
    (ringScalarExtensionPseudofunctor.map (RingCat.ofHom f).toLoc).toFunctor =
      ringScalarExtension f := by
  rfl

example (f : R →+* S) {P Q : FGProjectiveCat.{u} R} (a : P ⟶ Q)
    (x : (ringScalarExtension f).obj P) :
    (((ringScalarExtensionPseudofunctor.map (RingCat.ofHom f).toLoc).toFunctor.map a).hom.hom x) =
      ((ringScalarExtension f).map a).hom.hom x := by
  rfl

example (f : R →+* S) {P Q : FGProjectiveCat.{u} R} (a : P ⟶ Q)
    (x : (ringScalarExtension f).obj P) :
    ringScalarExtensionCoordinates f Q
        (((ringScalarExtensionPseudofunctor.map (RingCat.ofHom f).toLoc).toFunctor.map
          a).hom.hom x) =
      linearMap f a.hom.hom (ringScalarExtensionCoordinates f P x) := by
  exact LinearMap.congr_fun (ringScalarExtensionCoordinates_naturality f a) x

example (f : R →+* S) (g : S →+* T) :
    Cat.Hom.toNatIso
      (ringScalarExtensionPseudofunctor.mapComp (RingCat.ofHom f).toLoc
        (RingCat.ofHom g).toLoc) =
      (ringScalarExtensionCompIso f g).symm := by
  rfl

example :
    Cat.Hom.toNatIso
      (ringScalarExtensionPseudofunctor.mapId (LocallyDiscrete.mk (RingCat.of R))) =
      ringScalarExtensionIdIso R := by
  rfl

example (P : FGProjectiveCat.{u} R) (x : (ringScalarExtension (RingHom.id R)).obj P) :
    (((ringScalarExtensionPseudofunctor.mapId (LocallyDiscrete.mk
      (RingCat.of R))).hom.toNatTrans.app P).hom.hom x) =
      identityTensorLinearEquiv R P (ringScalarExtensionCoordinates (RingHom.id R) P x) := by
  exact ringScalarExtensionIdIso_hom_apply R P x

example (P : FGProjectiveCat.{u} R) (p : P) :
    (((ringScalarExtensionPseudofunctor.mapId (LocallyDiscrete.mk
      (RingCat.of R))).inv.toNatTrans.app P).hom.hom p) =
      (ringScalarExtensionCoordinates (RingHom.id R) P).symm
        (pure (RingHom.id R) P 1 p) := by
  exact ringScalarExtensionIdIso_inv_apply R P p

/-- A native compositor client computes the original ordered coefficient product. -/
theorem nativeScalarPseudofunctor_compositor_nested_pure
    (f : R →+* S) (g : S →+* T) (P : FGProjectiveCat.{u} R)
    (t : T) (s : S) (p : P) :
    ringScalarExtensionCoordinates (g.comp f) P
        (((ringScalarExtensionPseudofunctor.mapComp (RingCat.ofHom f).toLoc
          (RingCat.ofHom g).toLoc).inv.toNatTrans.app P).hom.hom
          ((ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
            (pure g ((ringScalarExtension f).obj P) t
              ((ringScalarExtensionCoordinates f P).symm (pure f P s p))))) =
      pure (g.comp f) P (t * g s) p := by
  exact ringScalarExtensionCompIso_hom_nested_pure f g P t s p

example (f : R →+* S) (g : S →+* T) (P : FGProjectiveCat.{u} R) (t : T) (p : P) :
    ((ringScalarExtensionPseudofunctor.mapComp (RingCat.ofHom f).toLoc
        (RingCat.ofHom g).toLoc).hom.toNatTrans.app P).hom.hom
        ((ringScalarExtensionCoordinates (g.comp f) P).symm (pure (g.comp f) P t p)) =
      (ringScalarExtensionCoordinates g ((ringScalarExtension f).obj P)).symm
        (pure g ((ringScalarExtension f).obj P) t
          ((ringScalarExtensionCoordinates f P).symm (pure f P 1 p))) := by
  exact ringScalarExtensionCompIso_inv_pure f g P t p

example (f : R →+* S) (g : S →+* T) {P Q : FGProjectiveCat.{u} R} (a : P ⟶ Q) :
    (ringScalarExtension f ⋙ ringScalarExtension g).map a ≫
        (ringScalarExtensionPseudofunctor.mapComp (RingCat.ofHom f).toLoc
          (RingCat.ofHom g).toLoc).inv.toNatTrans.app Q =
      (ringScalarExtensionPseudofunctor.mapComp (RingCat.ofHom f).toLoc
          (RingCat.ofHom g).toLoc).inv.toNatTrans.app P ≫
        (ringScalarExtension (g.comp f)).map a := by
  exact (ringScalarExtensionCompIso f g).hom.naturality a

example (f : R →+* S) :
    (ringScalarExtensionPseudofunctor.map (RingCat.ofHom f).toLoc).toFunctor.Additive := by
  infer_instance

example (f : R →+* S) :
    (ringScalarExtensionPseudofunctor.map (RingCat.ofHom f).toLoc).toFunctor.IsExact := by
  infer_instance

#print axioms FGProjectiveCat.ringScalarExtensionPseudofunctor
#print axioms nativeScalarPseudofunctor_compositor_nested_pure
