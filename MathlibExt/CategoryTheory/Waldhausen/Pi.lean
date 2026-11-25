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
# Pointwise Waldhausen structures on indexed families

The category of indexed families has a zero object and a named pointwise
Waldhausen structure when each component does. Pushouts along cofibrations
are assembled from the actual component universal properties. Evaluation
and common-source assembly of exact functors are Waldhausen exact.

The index, object and morphism universes are independent. The construction
requires no finite or nonempty index, additivity, gluing or cylinder data.
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

variable [∀ i, HasZeroObject (C i)] [∀ i, WaldhausenCategory (C i)]

/-- The pointwise Waldhausen structure on the original Pi category, as a named value. -/
@[instance_reducible]
def piWaldhausen : WaldhausenCategory (∀ i, C i) where
  cofibrations := MorphismProperty.pi (fun i => WaldhausenCategory.cofibrations (C := C i))
  weakEquivalences := MorphismProperty.pi (fun i => WaldhausenCategory.weakEquivalences (C := C i))
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
    have hf : WaldhausenCategory.cofibrations (C := C i) (e.inv ≫ f i) :=
      WaldhausenCategory.zero_isCofibration _ _
    have h := MorphismProperty.RespectsIso.precomp
      (WaldhausenCategory.cofibrations (C := C i)) e.hom (e.inv ≫ f i) hf
    exact (e.hom_inv_id_assoc (f i)) ▸ h
  cofibration_pushout := fun {X Y} i hi X' f => by
    classical
    choose P inl inr hP hcof using fun j =>
      WaldhausenCategory.cofibration_pushout (C := C j) (i j) (hi j) (X' j) (f j)
    exact ⟨P, inl, inr, Pi.isPushout_of_components C hP, hcof⟩

/-- Pi cofibrations are exactly the original component cofibrations. -/
@[simp]
theorem isCofibration_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    @IsCofibration (∀ i, C i) _ _ (piWaldhausen C) X Y f ↔
      ∀ i, IsCofibration (f i) := Iff.rfl

/-- Pi weak equivalences are exactly the original component weak equivalences. -/
@[simp]
theorem isWeakEquivalence_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    @IsWeakEquivalence (∀ i, C i) _ _ (piWaldhausen C) X Y f ↔
      ∀ i, IsWeakEquivalence (f i) := Iff.rfl

/-- Original coordinate evaluation is exact, with its actual mapped pushout faces. -/
theorem Pi.eval_isWaldhausenExact (j : I) :
    letI : WaldhausenCategory (∀ i, C i) := piWaldhausen C
    (Pi.eval C j).IsWaldhausenExact := by
  let _ : WaldhausenCategory (∀ i, C i) := piWaldhausen C
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
      WaldhausenCategory.cofibration_pushout (C := C k) (i k) (hi k) (Z k) (f k)
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

/-- Assemble exact functors with a common original source into the actual Pi target. -/
theorem Functor.IsWaldhausenExact.pi'
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategory A]
    (F : ∀ i, A ⥤ C i) (hF : ∀ i, (F i).IsWaldhausenExact) :
    letI : WaldhausenCategory (∀ i, C i) := piWaldhausen C
    (Functor.pi' F).IsWaldhausenExact := by
  let _ : WaldhausenCategory (∀ i, C i) := piWaldhausen C
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
