/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStableHoArrowTriangle
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Full represented exactness for every original ordinary-Ho arrow

The original Q/R representative and both complete comparison functions
transport the source-built Puppe exactness. Every Ho arrow, every Ho
target and each actual input/inclusion/boundary function is retained.
The ordinary suspension of both original endpoint comparisons supplies
the preceding exact position. No covariant, distinguished-triangle or
source-generator detection assertion is an input or a conclusion here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStableHoArrowExactness

open OrdinaryStableHoArrowTriangle

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "H" => toHomotopyCategory C
local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)

private theorem source_input_exact (F : Arrow C) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (OrdinaryStablePuppeConnecting.originalCofiberRestriction g Z hZ F E)
      (OrdinaryStablePuppeConnecting.inputRestriction g F E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact fun h => (OrdinaryStablePuppeConnecting.exact_at_target_original g Z hZ F E h).symm

private theorem source_boundary_exact (F : Arrow C) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (OrdinaryStablePuppeConnecting.connecting g Z hZ F E)
      (OrdinaryStablePuppeConnecting.originalCofiberRestriction g Z hZ F E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact fun h => (OrdinaryStablePuppeConnecting.exact_at_cofiber_original g Z hZ F E h).symm

private theorem source_suspension_exact (F : Arrow C) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (OrdinaryStablePuppeConnecting.suspensionRestriction g F E)
      (OrdinaryStablePuppeConnecting.connecting g Z hZ F E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact fun h => (OrdinaryStablePuppeConnecting.exact_at_suspension g Z hZ F E h).symm

/-- Every full Ho target kernel is the image of the actual original cofiber inclusion. -/
theorem exact_at_target {X Y : HomotopyCategory C} (f : X ⟶ Y)
    (E : HomotopyCategory C) (h : Y ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ a : cofiber g Z hZ f ⟶ E, inclusion g Z hZ f ≫ a = h) ↔ f ≫ h = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let F := OriginalOrdinaryHoArrowSource.sourceArrow g f
  have hp := (OriginalOrdinaryHoArrowSource.sourceArrowIso g f).hom.w.symm
  change (H).map F.hom ≫
    (OriginalOrdinaryHoArrowSource.targetIso g Y).hom =
      (OriginalOrdinaryHoArrowSource.sourceIso g X).hom ≫ f at hp
  have hq : OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F ≫
      (Iso.refl (cofiber g Z hZ f)).hom =
    (OriginalOrdinaryHoArrowSource.targetIso g Y).hom ≫ inclusion g Z hZ f := by
    simp only [Iso.refl_hom, inclusion, Iso.hom_inv_id_assoc]
    exact Category.comp_id (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F)
  have ht := (Preadditive.HomIsoExact.represented_source_iso
    ((H).map F.hom)
    (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F)
    f (inclusion g Z hZ f) (OriginalOrdinaryHoArrowSource.sourceIso g X)
    (OriginalOrdinaryHoArrowSource.targetIso g Y) (Iso.refl (cofiber g Z hZ f)) hp hq E).mpr
      (source_input_exact g Z hZ F E)
  exact (ht h).symm

/-- Every actual cofiber kernel is the image of the original boundary with its entire source comparison. -/
theorem exact_at_cofiber {X Y : HomotopyCategory C} (f : X ⟶ Y)
    (E : HomotopyCategory C) (h : cofiber g Z hZ f ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ a : (Σ).obj X ⟶ E, boundary g Z hZ f ≫ a = h) ↔ inclusion g Z hZ f ≫ h = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let F := OriginalOrdinaryHoArrowSource.sourceArrow g f
  let sx := (Σ).mapIso (OriginalOrdinaryHoArrowSource.sourceIso g X)
  have hp : OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F ≫
      (Iso.refl (cofiber g Z hZ f)).hom =
    (OriginalOrdinaryHoArrowSource.targetIso g Y).hom ≫ inclusion g Z hZ f := by
    simp only [Iso.refl_hom, inclusion, Iso.hom_inv_id_assoc]
    exact Category.comp_id (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F)
  have hq : OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫ sx.hom =
      (Iso.refl (cofiber g Z hZ f)).hom ≫ boundary g Z hZ f := by
    exact (Category.id_comp (boundary g Z hZ f)).symm
  have ht := (Preadditive.HomIsoExact.represented_source_iso
    (OrdinaryStablePuppeConnecting.originalTargetArrow g Z hZ F)
    (OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F)
    (inclusion g Z hZ f) (boundary g Z hZ f)
    (OriginalOrdinaryHoArrowSource.targetIso g Y) (Iso.refl (cofiber g Z hZ f)) sx hp hq E).mpr
      (source_boundary_exact g Z hZ F E)
  exact (ht h).symm

omit [(DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The actual ordinary suspension preserves the whole original representative Arrow square. -/
theorem suspension_square {X Y : HomotopyCategory C} (f : X ⟶ Y) :
    (Σ).map ((H).map (OriginalOrdinaryHoArrowSource.representative g f)) ≫
      (Σ).map (OriginalOrdinaryHoArrowSource.targetIso g Y).hom =
    (Σ).map (OriginalOrdinaryHoArrowSource.sourceIso g X).hom ≫ (Σ).map f := by
  have h := (OriginalOrdinaryHoArrowSource.sourceArrowIso g f).hom.w
  change (OriginalOrdinaryHoArrowSource.sourceIso g X).hom ≫ f =
    (H).map (OriginalOrdinaryHoArrowSource.representative g f) ≫
      (OriginalOrdinaryHoArrowSource.targetIso g Y).hom at h
  simpa only [Functor.map_comp] using ((Σ).congr_map h).symm

/-- The original suspended input image is exactly the boundary kernel at every complete Ho source. -/
theorem exact_at_suspension {X Y : HomotopyCategory C} (f : X ⟶ Y)
    (E : HomotopyCategory C) (h : (Σ).obj X ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ a : (Σ).obj Y ⟶ E, (Σ).map f ≫ a = h) ↔ boundary g Z hZ f ≫ h = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let F := OriginalOrdinaryHoArrowSource.sourceArrow g f
  let sx := (Σ).mapIso (OriginalOrdinaryHoArrowSource.sourceIso g X)
  let sy := (Σ).mapIso (OriginalOrdinaryHoArrowSource.targetIso g Y)
  have hp : OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F ≫ sx.hom =
      (Iso.refl (cofiber g Z hZ f)).hom ≫ boundary g Z hZ f := by
    exact (Category.id_comp (boundary g Z hZ f)).symm
  have hq : (Σ).map ((H).map (OriginalOrdinaryHoArrowSource.representative g f)) ≫ sy.hom =
      sx.hom ≫ (Σ).map f := suspension_square g f
  have ht := (Preadditive.HomIsoExact.represented_source_iso
    (OrdinaryStablePuppeConnecting.boundaryArrow g Z hZ F)
    ((Σ).map ((H).map (OriginalOrdinaryHoArrowSource.representative g f)))
    (boundary g Z hZ f) ((Σ).map f) (Iso.refl (cofiber g Z hZ f)) sx sy hp hq E).mpr
      (source_suspension_exact g Z hZ F E)
  exact (ht h).symm

/-- The full input restriction is the original caller Ho map as an additive group homomorphism. -/
def input {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E f

/-- The original cofiber inclusion gives its entire actual represented restriction homomorphism. -/
def restrict {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (inclusion g Z hZ f)

/-- The original source-comparison boundary gives its actual complete additive Hom function. -/
def connecting {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (boundary g Z hZ f)

/-- The actual ordinary suspension of the unchanged caller map gives the preceding group function. -/
def suspendedInput {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E ((Σ).map f)

/-- The three original complete represented functions satisfy Mathlib's exactness contract. -/
theorem represented_long_exact {X Y : HomotopyCategory C} (f : X ⟶ Y) (E : HomotopyCategory C) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    Function.Exact (restrict g Z hZ f E) (input g f E) ∧
      Function.Exact (connecting g Z hZ f E) (restrict g Z hZ f E) ∧
        Function.Exact (suspendedInput g f E) (connecting g Z hZ f E) := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact ⟨fun h => (exact_at_target g Z hZ f E h).symm,
    fun h => (exact_at_cofiber g Z hZ f E h).symm,
    fun h => (exact_at_suspension g Z hZ f E h).symm⟩

/-- Every whole Ho target morphism preserves the actual inclusion restriction function. -/
theorem restrict_target {X Y E E' : HomotopyCategory C} (f : X ⟶ Y) (t : E ⟶ E')
    (a : cofiber g Z hZ f ⟶ E) :
    restrict g Z hZ f E' (a ≫ t) = restrict g Z hZ f E a ≫ t := by
  change inclusion g Z hZ f ≫ (a ≫ t) = (inclusion g Z hZ f ≫ a) ≫ t
  exact (Category.assoc _ _ _).symm

/-- Every whole Ho target morphism preserves the full original boundary Hom function. -/
theorem connecting_target {X Y E E' : HomotopyCategory C} (f : X ⟶ Y) (t : E ⟶ E')
    (a : (Σ).obj X ⟶ E) :
    connecting g Z hZ f E' (a ≫ t) = connecting g Z hZ f E a ≫ t := by
  change boundary g Z hZ f ≫ (a ≫ t) = (boundary g Z hZ f ≫ a) ≫ t
  exact (Category.assoc _ _ _).symm

end HomotopicalAlgebra.OrdinaryStableHoArrowExactness
