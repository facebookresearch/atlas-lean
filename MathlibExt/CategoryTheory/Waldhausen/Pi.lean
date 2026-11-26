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

public import MathlibExt.CategoryTheory.Waldhausen.Basic
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor
public import MathlibExt.CategoryTheory.Pi.Limits
public import Mathlib.Tactic.Choose

/-!
# Pointwise cofibrations and weak equivalences for indexed families

Let C_i be categories with zero objects and WaldhausenCategoryWithoutGluing structures. On the
category ΠᵢC_i define cofibrations and weak equivalences componentwise. Zero objects and
pushouts along cofibrations are obtained componentwise, giving a named
WaldhausenCategoryWithoutGluing structure on the family category.

Coordinate evaluations are exact for these structures. A family of exact functors F_i from a
common source assembles into an exact functor X ↦ (F_i(X))_i. The index type is arbitrary, and
the source, target and indexing universes remain independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe w u v uA vA

open CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory

variable {I : Type w} (C : I → Type u) [∀ i, Category.{v} (C i)]

namespace Pi

private theorem property_eq_intersection (W : ∀ i, MorphismProperty (C i)) :
    MorphismProperty.pi W = ⨅ i, (W i).inverseImage (eval C i) := by
  funext X Y f
  have h := (MorphismProperty.iInf_iff
    (fun i => (W i).inverseImage (eval C i)) f).symm
  change (∀ i, W i (f i)) ↔ (⨅ i, (W i).inverseImage (eval C i)) f at h
  exact propext h

end Pi

variable [∀ i, HasZeroObject (C i)] [∀ i, WaldhausenCategoryWithoutGluing (C i)]

/-- Pointwise structure on a category of families.

For categories C_i with zero objects and WaldhausenCategoryWithoutGluing structures, define
the same structure on ΠᵢC_i by componentwise cofibrations and weak equivalences. Pushouts
along a cofibration use the component pushout objects and legs, and their universal properties
assemble in the family category. -/
@[instance_reducible]
def piWaldhausen : WaldhausenCategoryWithoutGluing (∀ i, C i) where
  cofibrations :=
    MorphismProperty.pi (fun i => WaldhausenCategoryWithoutGluing.cofibrations (C := C i))
  weakEquivalences :=
    MorphismProperty.pi (fun i => WaldhausenCategoryWithoutGluing.weakEquivalences (C := C i))
  cofibrations_isMultiplicative := by
    rw [Pi.property_eq_intersection C]
    infer_instance
  cofibrations_respectsIso := by
    rw [Pi.property_eq_intersection C]
    infer_instance
  weakEquivalences_isMultiplicative := by
    rw [Pi.property_eq_intersection C]
    infer_instance
  weakEquivalences_respectsIso := by
    rw [Pi.property_eq_intersection C]
    infer_instance
  zero_isCofibration := fun X f i => by
    have hzero := (Pi.isZero_iff C _).mp (isZero_zero (∀ i, C i)) i
    let e := hzero.iso (isZero_zero (C i))
    have hf : WaldhausenCategoryWithoutGluing.cofibrations (C := C i) (e.inv ≫ f i) :=
      WaldhausenCategoryWithoutGluing.zero_isCofibration _ _
    have h := MorphismProperty.RespectsIso.precomp
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C i)) e.hom (e.inv ≫ f i) hf
    exact (e.hom_inv_id_assoc (f i)) ▸ h
  cofibration_pushout := fun {X Y} i hi X' f => by
    classical
    choose P inl inr hP hcof using fun j =>
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C j) (i j) (hi j) (X' j) (f j)
    exact ⟨P, inl, inr, Pi.isPushout_of_components C hP, hcof⟩

/-- Component criterion for a family cofibration.

With the pointwise piWaldhausen structure, a family map f : X → Y is a cofibration if and only
if every f_i : X_i → Y_i is a cofibration in C_i. -/
@[simp]
theorem isCofibration_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    @IsCofibration (∀ i, C i) _ _ (piWaldhausen C) X Y f ↔
      ∀ i, IsCofibration (f i) := Iff.rfl

/-- Component criterion for a family weak equivalence.

With the pointwise piWaldhausen structure, a family map f : X → Y is a weak equivalence if and
only if every component f_i is a weak equivalence in C_i. -/
@[simp]
theorem isWeakEquivalence_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    @IsWeakEquivalence (∀ i, C i) _ _ (piWaldhausen C) X Y f ↔
      ∀ i, IsWeakEquivalence (f i) := Iff.rfl

/-- Exactness of coordinate evaluation for a pointwise structure.

For the pointwise WaldhausenCategoryWithoutGluing structure on ΠᵢC_i, evaluation at j is
exact: it preserves zero objects, cofibrations, weak equivalences and pushouts along
cofibrations. Its image of a chosen family pushout has the corresponding component legs. -/
theorem Pi.eval_isWaldhausenExact (j : I) :
    letI : WaldhausenCategoryWithoutGluing (∀ i, C i) := piWaldhausen C
    (Pi.eval C j).IsWaldhausenExact := by
  let _ : WaldhausenCategoryWithoutGluing (∀ i, C i) := piWaldhausen C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact (Pi.isZero_iff C X).mp hX j
  · intro X Y f hf
    exact hf j
  · intro X Y f hf
    exact hf j
  · intro X Y Z P i f inZ inY hi hP
    classical
    choose Q inl inr hQ hcof using fun k =>
      WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C k) (i k) (hi k) (Z k) (f k)
    have hwhole : IsPushout f i inl inr := Pi.isPushout_of_components C hQ
    let e : Q ≅ P := hwhole.isoIsPushout Z Y hP
    apply (hQ j).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Pi.isoApp e j)
    · change f j ≫ 𝟙 (Z j) = 𝟙 (X j) ≫ f j
      simp only [Category.comp_id, Category.id_comp]
    · change i j ≫ 𝟙 (Y j) = 𝟙 (X j) ≫ i j
      simp only [Category.comp_id, Category.id_comp]
    · change inl j ≫ e.hom j = 𝟙 (Z j) ≫ inZ j
      rw [Category.id_comp]
      exact congrArg (fun q : Z ⟶ P => q j) (hwhole.inl_isoIsPushout_hom Z Y hP)
    · change inr j ≫ e.hom j = 𝟙 (Y j) ≫ inY j
      rw [Category.id_comp]
      exact congrArg (fun q : Y ⟶ P => q j) (hwhole.inr_isoIsPushout_hom Z Y hP)

/-- Assembly of exact functors into a family category.

Let A have a zero object and WaldhausenCategoryWithoutGluing structure, and let F_i : A ⥤ C_i
be exact for the respective structures. The assembled functor A ⥤ ΠᵢC_i is exact for
piWaldhausen: its zero, cofibration, weak-equivalence and pushout conditions hold
componentwise. -/
theorem Functor.IsWaldhausenExact.pi'
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    (F : ∀ i, A ⥤ C i) (hF : ∀ i, (F i).IsWaldhausenExact) :
    letI : WaldhausenCategoryWithoutGluing (∀ i, C i) := piWaldhausen C
    (Functor.pi' F).IsWaldhausenExact := by
  let _ : WaldhausenCategoryWithoutGluing (∀ i, C i) := piWaldhausen C
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X hX
    exact Pi.isZero_of_components C (fun i => (hF i).map_isZero hX)
  · intro X Y f hf i
    exact (hF i).map_cofibration f hf
  · intro X Y f hf i
    exact (hF i).map_weakEquivalence f hf
  · intro X Y Z P i f inZ inY hi hP
    exact Pi.isPushout_of_components C (fun k => (hF k).map_pushout i f inZ inY hi hP)

end CategoryTheory
