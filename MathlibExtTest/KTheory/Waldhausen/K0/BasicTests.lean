/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.LinearAlgebra.Dimension.RankNullity
import MathlibExt.KTheory.Waldhausen.K0.Basic

/-! # Public clients of Waldhausen K₀

The integral split sequence tests additivity using an actual pushout. A separate
fixture treats epimorphisms as weak equivalences and tests `ℤ ⟶ 0`, whose
endpoints are not isomorphic. For finite-dimensional rational vector spaces,
the dimension lift takes the one-dimensional class to `1`.
-/

open CategoryTheory Limits ZeroObject WaldhausenKTheory

namespace MathlibExtTest.WaldhausenK0

private local instance addCommGrpWaldhausen : WaldhausenCategoryWithoutGluing AddCommGrpCat where
  cofibrations := MorphismProperty.monomorphisms _
  weakEquivalences := MorphismProperty.isomorphisms _
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration _ f := mono_of_source_iso_zero f (Iso.refl (0 : AddCommGrpCat))
  cofibration_pushout i hi _ f := by
    have : Mono i := hi
    exact ⟨pushout f i, pushout.inl f i, pushout.inr f i, IsPushout.of_hasPushout f i,
      Abelian.mono_pushout_of_mono_g f i⟩

/-- The projection onto the second summand is the cofiber of the first inclusion. -/
private theorem biproductCofiber (X Y : AddCommGrpCat) :
    IsCofibrationSequence (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) := by
  refine ⟨?_, 0, 0, ?_⟩
  · change Mono (biprod.inl : X ⟶ X ⊞ Y)
    infer_instance
  have comm : (0 : X ⟶ (0 : AddCommGrpCat)) ≫ (0 : (0 : AddCommGrpCat) ⟶ Y) =
      biprod.inl ≫ (biprod.snd : X ⊞ Y ⟶ Y) := by simp
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk comm
    (fun s => biprod.inr ≫ s.inr) ?_ ?_ ?_)
  · intro s
    exact (isZero_zero _).eq_of_src _ _
  · intro s
    apply biprod.hom_ext'
    · simp only [biprod.inl_snd_assoc, zero_comp]
      simpa only [zero_comp] using s.condition
    · simp only [biprod.inr_snd_assoc]
  · intro s m _ hm
    rw [← hm, ← Category.assoc, biprod.inr_snd, Category.id_comp]

private abbrev Z : AddCommGrpCat := AddCommGrpCat.of ℤ

example : (K0.mk (Z ⊞ Z) : K0 AddCommGrpCat) = K0.mk Z + K0.mk Z :=
  K0.mk_eq_of_cofibrationSequence (biproductCofiber Z Z)

example : (K0.mk (0 : AddCommGrpCat) : K0 AddCommGrpCat) = 0 := by simp

section EpiClient

/-- Test a weak equivalence that is not an isomorphism, using epis for this fixture. -/
private local instance (priority := high) : WaldhausenCategoryWithoutGluing AddCommGrpCat where
  __ := addCommGrpWaldhausen
  weakEquivalences := MorphismProperty.epimorphisms _
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance

example : (¬ Nonempty (Z ≅ (0 : AddCommGrpCat))) ∧
    (K0.mk Z : K0 AddCommGrpCat) = K0.mk (0 : AddCommGrpCat) := by
  let f : Z ⟶ (0 : AddCommGrpCat) := 0
  refine ⟨?_, K0.mk_eq_of_weakEquivalence f (epi_of_target_iso_zero f (Iso.refl _))⟩
  rintro ⟨e⟩
  have hz : IsZero Z := (isZero_zero _).of_iso e
  have h := hz.eq_of_src (𝟙 Z) 0
  have h1 := congrArg (fun f : Z ⟶ Z => f (1 : ℤ)) h
  simp at h1

end EpiClient

private abbrev Vect := FGModuleCat.{0} ℚ

private local instance : WaldhausenCategoryWithoutGluing Vect where
  cofibrations := MorphismProperty.monomorphisms _
  weakEquivalences := MorphismProperty.isomorphisms _
  cofibrations_isMultiplicative := inferInstance
  cofibrations_respectsIso := inferInstance
  weakEquivalences_isMultiplicative := inferInstance
  weakEquivalences_respectsIso := inferInstance
  zero_isCofibration _ f := mono_of_source_iso_zero f (Iso.refl (0 : Vect))
  cofibration_pushout i hi _ f := by
    have : Mono i := hi
    exact ⟨pushout f i, pushout.inl f i, pushout.inr f i, IsPushout.of_hasPushout f i,
      Abelian.mono_pushout_of_mono_g f i⟩

private noncomputable def dimension : Skeleton Vect → ℤ :=
  Quotient.lift (fun X : Vect => (Module.finrank ℚ X : ℤ)) fun _ _ ⟨e⟩ =>
    congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv e).finrank_eq

private theorem dimension_weak {X Y : Vect} (f : X ⟶ Y) (h : IsWeakEquivalence f) :
    dimension (toSkeleton X) = dimension (toSkeleton Y) := by
  have : IsIso f := h
  exact congrArg Int.ofNat (FGModuleCat.isoToLinearEquiv (asIso f)).finrank_eq

/-- A cofiber is the quotient by the range of the first map; apply rank-nullity. -/
private theorem dimension_cofiber {X Y Z : Vect} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : IsCofibrationSequence f g) :
    dimension (toSkeleton Y) = dimension (toSkeleton X) + dimension (toSkeleton Z) := by
  obtain ⟨hf, a, q, push⟩ := h
  have : Mono f := hf
  let F := forget₂ Vect (ModuleCat.{0} ℚ)
  have hp := F.map_isPushout push
  have zh : IsZero (F.obj (0 : Vect)) := F.map_isZero (isZero_zero _)
  have hfg : F.map f ≫ F.map g = 0 := by
    rw [← hp.w, zh.eq_of_src (F.map q) 0, comp_zero]
  have hc : IsColimit (CokernelCofork.ofπ (F.map g) hfg) := by
    let commute {W : ModuleCat ℚ} (k : F.obj Y ⟶ W) (hk : F.map f ≫ k = 0) :
        F.map a ≫ 0 = F.map f ≫ k := by rw [hk, comp_zero]
    refine CokernelCofork.IsColimit.ofπ _ _ (fun k hk => hp.desc 0 k (commute k hk))
      (fun k hk => hp.inr_desc _ _ (commute k hk)) ?_
    intro W k hk m hm
    exact hp.hom_ext (zh.eq_of_src _ _) (hm.trans (hp.inr_desc _ _ (commute k hk)).symm)
  let e := hc.coconePointUniqueUpToIso (ModuleCat.cokernelIsColimit (F.map f))
  have hquot : Module.finrank ℚ Z = Module.finrank ℚ (Y ⧸ (F.map f).hom.range) :=
    e.toLinearEquiv.finrank_eq
  have hinj : Function.Injective (F.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hrange : Module.finrank ℚ (F.map f).hom.range = Module.finrank ℚ X :=
    (LinearEquiv.ofInjective _ hinj).finrank_eq.symm
  have hfinite : Module.Finite ℚ (F.obj Y) := (inferInstance : Module.Finite ℚ Y)
  have hr := (F.map f).hom.range.finrank_quotient_add_finrank
  change Module.finrank ℚ (Y ⧸ (F.map f).hom.range) + _ = Module.finrank ℚ Y at hr
  rw [← hquot, hrange, add_comm] at hr
  change (Module.finrank ℚ Y : ℤ) = (Module.finrank ℚ X : ℤ) + (Module.finrank ℚ Z : ℤ)
  exact_mod_cast hr.symm

private noncomputable def dimensionLift : K0 Vect →+ ℤ :=
  K0.lift dimension dimension_weak dimension_cofiber

example : dimensionLift (K0.mk (FGModuleCat.of ℚ ℚ)) = 1 := by
  rw [dimensionLift, K0.lift_mk]
  change (Module.finrank ℚ ℚ : ℤ) = 1
  simp

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

example {A : Type*} [AddCommGroup A] (φ : Skeleton C → A)
    (hw : ∀ {X Y : C} (f : X ⟶ Y), IsWeakEquivalence f → φ (toSkeleton X) = φ (toSkeleton Y))
    (hc : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      IsCofibrationSequence f g → φ (toSkeleton Y) = φ (toSkeleton X) + φ (toSkeleton Z)) :
    ∃! F : K0 C →+ A, ∀ X : C, F (K0.mk X) = φ (toSkeleton X) :=
  ⟨K0.lift φ hw hc, fun X => K0.lift_mk φ hw hc X, fun F hF => K0.lift_unique φ hw hc F hF⟩

end MathlibExtTest.WaldhausenK0
