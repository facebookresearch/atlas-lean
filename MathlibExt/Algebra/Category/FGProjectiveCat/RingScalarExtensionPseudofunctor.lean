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

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionFunctorCoherence
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The native scalar-extension pseudofunctor on associative rings

The objects are the original finite-projective categories and the arrows are
literally `ringScalarExtension`. The identity comparison is the original
`ringScalarExtensionIdIso`; the composition comparison is the inverse of the
original `ringScalarExtensionCompIso`, matching Mathlib's pseudofunctor convention.

The three coherence obligations follow from the whole native unit and
associativity equations. Their tensor constructions and their independent-ring
universe supplier are unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.Bicategory

universe u uR uS uT uU

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
  [Ring R] [Ring S] [Ring T] [Ring U]

/-- The inverse native comparisons cancel the full original associativity route. -/
theorem ringScalarExtensionCompIso_inv_associator
    (f : R →+* S) (g : S →+* T) (h : T →+* U) :
    (ringScalarExtensionCompIso (g.comp f) h).inv ≫
        (Functor.isoWhiskerRight (ringScalarExtensionCompIso f g) (ringScalarExtension h)).inv ≫
        (Functor.associator (ringScalarExtension f) (ringScalarExtension g)
          (ringScalarExtension h)).hom ≫
        (Functor.isoWhiskerLeft (ringScalarExtension f)
          (ringScalarExtensionCompIso g h)).hom ≫
        (ringScalarExtensionCompIso f (h.comp g)).hom =
      𝟙 (ringScalarExtension (h.comp (g.comp f))) := by
  have hcoh := congrArg Iso.hom (ringScalarExtensionCompIso_assoc f g h)
  simp only [Iso.trans_hom] at hcoh
  rw [← hcoh]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- The inverse native comparison cancels the actual initial-identity route. -/
theorem ringScalarExtensionCompIso_inv_leftUnitor (f : R →+* S) :
    (ringScalarExtensionCompIso (RingHom.id R) f).inv ≫
        (Functor.isoWhiskerRight (ringScalarExtensionIdIso R) (ringScalarExtension f)).hom ≫
        (ringScalarExtension f).leftUnitor.hom =
      eqToHom (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.comp_id f)) := by
  have hcoh := congrArg Iso.hom (ringScalarExtensionCompIso_id_left f)
  simp only [Iso.trans_hom] at hcoh
  rw [← hcoh]
  simp

/-- The inverse native comparison cancels the actual terminal-identity route. -/
theorem ringScalarExtensionCompIso_inv_rightUnitor (f : R →+* S) :
    (ringScalarExtensionCompIso f (RingHom.id S)).inv ≫
        (Functor.isoWhiskerLeft (ringScalarExtension f) (ringScalarExtensionIdIso S)).hom ≫
        (ringScalarExtension f).rightUnitor.hom =
      eqToHom (congrArg (fun k : R →+* S => ringScalarExtension k) (RingHom.id_comp f)) := by
  have hcoh := congrArg Iso.hom (ringScalarExtensionCompIso_id_right f)
  simp only [Iso.trans_hom] at hcoh
  rw [← hcoh]
  simp

/-- The covariant associative-ring pseudofunctor with the actual native scalar functors. -/
@[implicit_reducible]
def ringScalarExtensionPseudofunctor :
    Pseudofunctor (LocallyDiscrete RingCat.{u}) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (FGProjectiveCat.{u} (R : Type u)))
    (fun f => (ringScalarExtension f.hom).toCatHom)
    (fun R => Cat.Hom.isoMk (ringScalarExtensionIdIso (R : Type u)))
    (fun f g => Cat.Hom.isoMk (ringScalarExtensionCompIso f.hom g.hom).symm) ?_ ?_ ?_
  · intro R S T U f g h
    apply Cat.Hom₂.ext
    change (ringScalarExtensionCompIso (g.hom.comp f.hom) h.hom).inv ≫
        (Functor.isoWhiskerRight (ringScalarExtensionCompIso f.hom g.hom)
          (ringScalarExtension h.hom)).inv ≫
        (Functor.associator (ringScalarExtension f.hom) (ringScalarExtension g.hom)
          (ringScalarExtension h.hom)).hom ≫
        (Functor.isoWhiskerLeft (ringScalarExtension f.hom)
          (ringScalarExtensionCompIso g.hom h.hom)).hom ≫
        (ringScalarExtensionCompIso f.hom (h.hom.comp g.hom)).hom =
      𝟙 (ringScalarExtension (h.hom.comp (g.hom.comp f.hom)))
    exact ringScalarExtensionCompIso_inv_associator f.hom g.hom h.hom
  · intro R S f
    apply Cat.Hom₂.ext
    change (ringScalarExtensionCompIso (RingHom.id (R : Type u)) f.hom).inv ≫
        (Functor.isoWhiskerRight (ringScalarExtensionIdIso (R : Type u))
          (ringScalarExtension f.hom)).hom ≫
        (ringScalarExtension f.hom).leftUnitor.hom =
      eqToHom (congrArg (fun k : (R : Type u) →+* (S : Type u) => ringScalarExtension k)
        (RingHom.comp_id f.hom))
    exact ringScalarExtensionCompIso_inv_leftUnitor f.hom
  · intro R S f
    apply Cat.Hom₂.ext
    change (ringScalarExtensionCompIso f.hom (RingHom.id (S : Type u))).inv ≫
        (Functor.isoWhiskerLeft (ringScalarExtension f.hom)
          (ringScalarExtensionIdIso (S : Type u))).hom ≫
        (ringScalarExtension f.hom).rightUnitor.hom =
      eqToHom (congrArg (fun k : (R : Type u) →+* (S : Type u) => ringScalarExtension k)
        (RingHom.id_comp f.hom))
    exact ringScalarExtensionCompIso_inv_rightUnitor f.hom

/-- The pseudofunctor object inherits the original native preadditive structure. -/
instance ringScalarExtensionPseudofunctorObjPreadditive
    (R : LocallyDiscrete RingCat.{u}) : Preadditive (ringScalarExtensionPseudofunctor.obj R) :=
  inferInstanceAs (Preadditive (FGProjectiveCat.{u} (R.as : Type u)))

/-- The pseudofunctor object inherits the original native zero-object property. -/
instance ringScalarExtensionPseudofunctorObjHasZeroObject
    (R : LocallyDiscrete RingCat.{u}) :
    CategoryTheory.Limits.HasZeroObject (ringScalarExtensionPseudofunctor.obj R) :=
  inferInstanceAs (CategoryTheory.Limits.HasZeroObject (FGProjectiveCat.{u} (R.as : Type u)))

/-- The original native binary biproducts are retained at every pseudofunctor object. -/
instance ringScalarExtensionPseudofunctorObjHasBinaryBiproducts
    (R : LocallyDiscrete RingCat.{u}) :
    CategoryTheory.Limits.HasBinaryBiproducts (ringScalarExtensionPseudofunctor.obj R) :=
  inferInstanceAs (CategoryTheory.Limits.HasBinaryBiproducts (FGProjectiveCat.{u} (R.as : Type u)))

/-- The pseudofunctor object inherits the same original split exact structure. -/
instance ringScalarExtensionPseudofunctorObjExactCategory
    (R : LocallyDiscrete RingCat.{u}) : ExactCategory (ringScalarExtensionPseudofunctor.obj R) :=
  inferInstanceAs (ExactCategory (FGProjectiveCat.{u} (R.as : Type u)))

/-- The pseudofunctor keeps the original native category of each ring. -/
@[simp] theorem ringScalarExtensionPseudofunctor_obj (R : LocallyDiscrete RingCat.{u}) :
    ringScalarExtensionPseudofunctor.obj R = Cat.of (FGProjectiveCat.{u} (R.as : Type u)) :=
  rfl

/-- Every arrow is the actual native scalar-extension functor. -/
@[simp] theorem ringScalarExtensionPseudofunctor_map
    {R S : LocallyDiscrete RingCat.{u}} (f : R ⟶ S) :
    (ringScalarExtensionPseudofunctor.map f).toFunctor = ringScalarExtension f.as.hom :=
  rfl

/-- The whole identity comparison recovers the original native identity isomorphism. -/
@[simp] theorem ringScalarExtensionPseudofunctor_mapId
    (R : LocallyDiscrete RingCat.{u}) :
    Cat.Hom.toNatIso (ringScalarExtensionPseudofunctor.mapId R) =
      ringScalarExtensionIdIso (R.as : Type u) :=
  rfl

/-- The whole composition comparison is the inverse of the original native comparison. -/
@[simp] theorem ringScalarExtensionPseudofunctor_mapComp
    {R S T : LocallyDiscrete RingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Cat.Hom.toNatIso (ringScalarExtensionPseudofunctor.mapComp f g) =
      (ringScalarExtensionCompIso f.as.hom g.as.hom).symm :=
  rfl

/-- The native pseudofunctor arrows retain their actual additive structures. -/
instance ringScalarExtensionPseudofunctorMapAdditive
    {R S : LocallyDiscrete RingCat.{u}} (f : R ⟶ S) :
    (ringScalarExtensionPseudofunctor.map f).toFunctor.Additive := by
  change (ringScalarExtension f.as.hom).Additive
  infer_instance

/-- The native pseudofunctor arrows retain split exactness without flatness. -/
instance ringScalarExtensionPseudofunctorMapIsExact
    {R S : LocallyDiscrete RingCat.{u}} (f : R ⟶ S) :
    (ringScalarExtensionPseudofunctor.map f).toFunctor.IsExact := by
  change (ringScalarExtension f.as.hom).IsExact
  infer_instance

end FGProjectiveCat
