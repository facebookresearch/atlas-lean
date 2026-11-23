/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.KTheory.Waldhausen.K0.Basic

/-!
# Functoriality of Waldhausen K₀ without gluing

An exact functor preserves the weak-equivalence and cofibration-sequence
relations. It therefore induces an additive map on K₀. Precomposing a
coefficient lift with this map is the lift of the pulled-back coefficients.
-/

public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace WaldhausenKTheory

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {E : Type u₃} [Category.{v₃} E] [HasZeroObject E] [WaldhausenCategoryWithoutGluing E]

private noncomputable def generator (F : C ⥤ D) : Skeleton C → K0 D :=
  fun s => K0.mk (F.obj ((fromSkeleton C).obj s))

omit [HasZeroObject C] [WaldhausenCategoryWithoutGluing C] in
private lemma generator_toSkeleton (F : C ⥤ D) (X : C) :
    generator F (toSkeleton X) = K0.mk (F.obj X) :=
  K0.mk_eq_of_iso (F.mapIso (fromSkeletonToSkeletonIso X))

private lemma generator_weak (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {X Y : C} (f : X ⟶ Y) (h : IsWeakEquivalence f) :
    generator F (toSkeleton X) = generator F (toSkeleton Y) := by
  simpa only [generator_toSkeleton] using
    K0.mk_eq_of_weakEquivalence (F.map f) (hF.map_weakEquivalence f h)

private lemma generator_cofiber (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : IsCofibrationSequence f g) :
    generator F (toSkeleton Y) = generator F (toSkeleton X) + generator F (toSkeleton Z) := by
  simpa only [generator_toSkeleton] using
    K0.mk_eq_of_cofibrationSequence (hF.map_cofibrationSequence h)

/-- The group homomorphism induced by an exact functor of Waldhausen structures. -/
noncomputable def K0.mapOfWaldhausenExact (F : C ⥤ D)
    (hF : F.IsWaldhausenExact) : K0 C →+ K0 D :=
  K0.lift (generator F) (generator_weak F hF) (generator_cofiber F hF)

/-- The map sends an object class to the class of its image. -/
@[simp]
theorem K0.mapOfWaldhausenExact_mk (F : C ⥤ D) (hF : F.IsWaldhausenExact) (X : C) :
    K0.mapOfWaldhausenExact F hF (K0.mk X) = K0.mk (F.obj X) :=
  (K0.lift_mk (generator F) (generator_weak F hF) (generator_cofiber F hF) X).trans
    (generator_toSkeleton F X)

/-- The identity functor induces the identity map on Waldhausen K₀. -/
@[simp]
theorem K0.mapOfWaldhausenExact_id :
    K0.mapOfWaldhausenExact (Functor.id C) Functor.IsWaldhausenExact.id =
      AddMonoidHom.id (K0 C) := by
  apply K0.hom_ext
  intro X
  simp

/-- The map associated with a composite is the composite of the two induced maps. -/
theorem K0.mapOfWaldhausenExact_comp (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    K0.mapOfWaldhausenExact (F ⋙ G) (hF.comp hG) =
      (K0.mapOfWaldhausenExact G hG).comp (K0.mapOfWaldhausenExact F hF) := by
  apply K0.hom_ext
  intro X
  simp

/-- A coefficient lift precomposed with the induced K₀ map is the lift of
coefficients pulled back along the functor on isomorphism classes. -/
theorem K0.lift_comp_mapOfWaldhausenExact (F : C ⥤ D) (hF : F.IsWaldhausenExact)
    {A : Type*} [AddCommGroup A] (φ : Skeleton D → A)
    (hw : ∀ {X Y : D} (f : X ⟶ Y), IsWeakEquivalence f → φ (toSkeleton X) = φ (toSkeleton Y))
    (hc : ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsCofibrationSequence f g → φ (toSkeleton Y) = φ (toSkeleton X) + φ (toSkeleton Z)) :
    (K0.lift φ hw hc).comp (K0.mapOfWaldhausenExact F hF) =
      K0.lift (φ ∘ F.mapSkeleton.obj)
        (fun f hf => by
          simpa only [Function.comp_apply, Functor.mapSkeleton_obj_toSkeleton] using
            hw (F.map f) (hF.map_weakEquivalence f hf))
        (fun f g h => by
          simpa only [Function.comp_apply, Functor.mapSkeleton_obj_toSkeleton] using
            hc (F.map f) (F.map g) (hF.map_cofibrationSequence h)) := by
  apply K0.hom_ext
  intro X
  simp [Function.comp_apply, Functor.mapSkeleton_obj_toSkeleton]

end WaldhausenKTheory
