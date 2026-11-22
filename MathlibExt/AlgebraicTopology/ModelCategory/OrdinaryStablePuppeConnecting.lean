/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryStablePuppeGroups
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryFramingComparison
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryPuppeLoopSequence
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The actual additive ordinary-suspension Puppe connecting map

The original cone boundary is followed by the SAME full framing
suspension comparison. This gives the genuine ordinary-suspension
boundary and additive connecting homomorphism. The original weak rotation
comparison identifies its image with the SAME original next Puppe map.
Every source/target object and both original comparison functions remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryStablePuppeConnecting

open OrdinaryStablePuppeGroups

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)
  [(DerivedSuspensionLoopAdjunction.suspension
    (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence]

local notation "Σ" => DerivedSuspensionLoopAdjunction.suspension
  (GeneratedFunctorialReplacements.fromGeneration g)
local notation "adjOrd" => DerivedSuspensionLoopAdjunction.adjunction
  (GeneratedFunctorialReplacements.fromGeneration g)

/-- The original generated suspension source is the actual ordinary suspension of the original input source. -/
def framingSourceIso (F : Arrow C) : suspendedHoSource g Z hZ F ≅
    (Σ).obj ((toHomotopyCategory C).obj F.left) := by
  unfold suspendedHoSource suspendedSource
  exact (GeneratedOrdinaryFramingComparison.comparison g Z hZ).app F.left

/-- The full original boundary is followed by the SAME original ordinary framing comparison. -/
def boundaryArrow (F : Arrow C) : cofiberHo g Z hZ F ⟶
    (Σ).obj ((toHomotopyCategory C).obj F.left) :=
  OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F ≫ (framingSourceIso g Z hZ F).hom

/-- The ordinary-suspension connecting homomorphism retains the entire original boundary word. -/
def connecting (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (boundaryArrow g Z hZ F)

/-- The complete connecting function is original boundary followed by original ordinary framing comparison. -/
theorem connecting_apply (F : Arrow C) (E : HomotopyCategory C)
    (h : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    connecting g Z hZ F E h =
      OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F ≫ (framingSourceIso g Z hZ F).hom ≫ h := by
  change (OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F ≫ (framingSourceIso g Z hZ F).hom) ≫ h = _
  exact Category.assoc _ _ _

/-- The SAME original three-step weak rotation retains the original cone suspension endpoint. -/
def coneRotationIso (F : Arrow C) :
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 3).obj F) ≅
      suspendedHoSource g Z hZ F := by
  unfold suspendedHoSource suspendedSource
  exact (GeneratedOrdinaryPuppe.shiftHoIso g Z hZ 0).app F

/-- Both complete original comparisons give the actual ordinary-suspension rotation Iso. -/
def rotationIso (F : Arrow C) :
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 3).obj F) ≅
      (Σ).obj ((toHomotopyCategory C).obj F.left) :=
  coneRotationIso g Z hZ F ≪≫ framingSourceIso g Z hZ F

/-- The original step retains the actual original weak-rotation readback. -/
def nextArrow (F : Arrow C) : cofiberHo g Z hZ F ⟶
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 3).obj F) := by
  unfold cofiberHo
  exact (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 2).app F)

omit [HasZeroObject C] [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  [(DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The original cone boundary keeps the complete original weak-rotation recovery law. -/
theorem cone_boundary_recovered (F : Arrow C) :
    nextArrow g Z hZ F ≫ (coneRotationIso g Z hZ F).hom =
      OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F := by
  unfold nextArrow coneRotationIso OrdinaryStablePuppeGroups.boundaryArrow
  unfold cofiberHo suspendedHoSource suspendedSource
  simp only [id_eq]
  change (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 2).app F) ≫
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.shiftComparison g Z hZ 0).app F) =
    (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.boundary g Z hZ).app F)
  rw [← Functor.map_comp, GeneratedOrdinaryPuppe.boundary_recovered]

omit [(DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The complete ordinary boundary is precisely the original next step followed by both original Isos. -/
theorem boundary_recovered (F : Arrow C) :
    nextArrow g Z hZ F ≫ (rotationIso g Z hZ F).hom = boundaryArrow g Z hZ F := by
  change nextArrow g Z hZ F ≫
      ((coneRotationIso g Z hZ F).hom ≫ (framingSourceIso g Z hZ F).hom) =
    OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F ≫ (framingSourceIso g Z hZ F).hom
  rw [← Category.assoc, cone_boundary_recovered]

/-- The entire original Arrow square retains the original Q-cofiber map. -/
def cofiberMap {F G : Arrow C} (a : F ⟶ G) : cofiberHo g Z hZ F ⟶ cofiberHo g Z hZ G := by
  unfold cofiberHo
  exact (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).map a)

/-- The whole original source square retains the same original Q-image suspension map. -/
def sourceSuspensionMap {F G : Arrow C} (a : F ⟶ G) :
    suspendedHoSource g Z hZ F ⟶ suspendedHoSource g Z hZ G := by
  unfold suspendedHoSource suspendedSource
  exact (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.suspension g Z hZ).map
    ((GeneratedFunctorialReplacements.Q g).map a.left))

omit [(DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The SAME actual framing comparison is natural on each complete original source component. -/
theorem framing_naturality {F G : Arrow C} (a : F ⟶ G) :
    sourceSuspensionMap g Z hZ a ≫ (framingSourceIso g Z hZ G).hom =
      (framingSourceIso g Z hZ F).hom ≫ (Σ).map ((toHomotopyCategory C).map a.left) := by
  unfold sourceSuspensionMap framingSourceIso suspendedHoSource suspendedSource
  simp only [id_eq]
  change (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.suspension g Z hZ).map
      ((GeneratedFunctorialReplacements.Q g).map a.left)) ≫
        (GeneratedOrdinaryFramingComparison.comparison g Z hZ).hom.app G.left =
    (GeneratedOrdinaryFramingComparison.comparison g Z hZ).hom.app F.left ≫
      (Σ).map ((toHomotopyCategory C).map a.left)
  exact (GeneratedOrdinaryFramingComparison.comparison g Z hZ).hom.naturality a.left

omit [HasZeroObject C] [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  [(DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- The actual original cone boundary retains the full original source Arrow naturality square. -/
theorem cone_boundary_naturality {F G : Arrow C} (a : F ⟶ G) :
    cofiberMap g Z hZ a ≫ OrdinaryStablePuppeGroups.boundaryArrow g Z hZ G =
      OrdinaryStablePuppeGroups.boundaryArrow g Z hZ F ≫ sourceSuspensionMap g Z hZ a := by
  unfold cofiberMap OrdinaryStablePuppeGroups.boundaryArrow sourceSuspensionMap
  unfold cofiberHo suspendedHoSource suspendedSource
  simp only [id_eq]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (toHomotopyCategory C).congr_map ((GeneratedOrdinaryPuppe.boundary g Z hZ).naturality a)

omit [(DerivedSuspensionLoopAdjunction.suspension (GeneratedFunctorialReplacements.fromGeneration g)).IsEquivalence] in
/-- Every original input Arrow square preserves the full actual ordinary-suspension boundary. -/
theorem boundary_naturality {F G : Arrow C} (a : F ⟶ G) :
    cofiberMap g Z hZ a ≫ boundaryArrow g Z hZ G =
      boundaryArrow g Z hZ F ≫ (Σ).map ((toHomotopyCategory C).map a.left) := by
  unfold boundaryArrow
  rw [← Category.assoc, cone_boundary_naturality, Category.assoc, framing_naturality, ← Category.assoc]

/-- The full ordinary connecting function is natural on BOTH original source-square legs. -/
theorem connecting_source {F G : Arrow C} (a : F ⟶ G) (E : HomotopyCategory C)
    (h : (Σ).obj ((toHomotopyCategory C).obj G.left) ⟶ E) :
    connecting g Z hZ F E ((Σ).map ((toHomotopyCategory C).map a.left) ≫ h) =
      cofiberMap g Z hZ a ≫ connecting g Z hZ G E h := by
  change boundaryArrow g Z hZ F ≫ ((Σ).map ((toHomotopyCategory C).map a.left) ≫ h) =
    cofiberMap g Z hZ a ≫ (boundaryArrow g Z hZ G ≫ h)
  rw [← Category.assoc, ← boundary_naturality, Category.assoc]

/-- Every full Ho target arrow preserves the SAME actual connecting homomorphism function. -/
theorem connecting_target (F : Arrow C) {E E' : HomotopyCategory C} (a : E ⟶ E')
    (h : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    connecting g Z hZ F E' (h ≫ a) = connecting g Z hZ F E h ≫ a := by
  change boundaryArrow g Z hZ F ≫ (h ≫ a) = (boundaryArrow g Z hZ F ≫ h) ≫ a
  exact (Category.assoc _ _ _).symm

/-- The original target leg induces the complete original cofiber restriction homomorphism. -/
def targetArrow (F : Arrow C) :
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 1).obj F) ⟶
      cofiberHo g Z hZ F := by
  unfold cofiberHo
  exact (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F)

/-- The cofiber restriction retains the original target leg as an additive group map. -/
def cofiberRestriction (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (targetArrow g Z hZ F)

private theorem image_precomp_iso {D : Type*} [Category* D] {U V W E : D}
    (p : U ⟶ V) (e : V ≅ W) (f : U ⟶ E) :
    (∃ h : W ⟶ E, (p ≫ e.hom) ≫ h = f) ↔ (∃ h : V ⟶ E, p ≫ h = f) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨e.hom ≫ h, (Category.assoc _ _ _).symm.trans hh⟩
  · rintro ⟨h, hh⟩
    refine ⟨e.inv ≫ h, ?_⟩
    rw [Category.assoc, ← Category.assoc e.hom e.inv h, e.hom_inv_id, Category.id_comp]
    exact hh

/-- The actual ordinary-suspension connecting image is the SAME original cofiber zero kernel at every Ho target. -/
theorem exact_at_cofiber (F : Arrow C) (E : HomotopyCategory C) (f : cofiberHo g Z hZ F ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E, connecting g Z hZ F E h = f) ↔
      cofiberRestriction g Z hZ F E f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  have hImage := image_precomp_iso (nextArrow g Z hZ F) (rotationIso g Z hZ F) f
  rw [boundary_recovered] at hImage
  have hExact : (∃ h : (toHomotopyCategory C).obj
      ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 3).obj F) ⟶ E, nextArrow g Z hZ F ≫ h = f) ↔
      targetArrow g Z hZ F ≫ f = 0 := by
    unfold nextArrow targetArrow cofiberHo at *
    simp only [id_eq]
    have ht := OrdinaryStablePuppeGroups.exact_at g Z hZ 1 F E f
    simpa only [restriction_apply] using ht
  exact hImage.trans hExact

/-- The target comparison is the SAME original Q counit, with both actual Iso directions. -/
def targetCounitIso (F : Arrow C) :
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 1).obj F) ≅
      (toHomotopyCategory C).obj F.right := by
  let : IsIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app F.right)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (GeneratedFunctorialReplacements.counit_weak g F.right)
  exact asIso ((toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app F.right))

/-- The original target Y injects by the SAME inverse original counit and unchanged original cofiber target leg. -/
def originalTargetArrow (F : Arrow C) : (toHomotopyCategory C).obj F.right ⟶ cofiberHo g Z hZ F :=
  (targetCounitIso g Z hZ F).inv ≫ targetArrow g Z hZ F

/-- The full original-Y restriction is the actual additive precomposition function. -/
def originalCofiberRestriction (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E (originalTargetArrow g Z hZ F)

private theorem zero_precomp_iso {D : Type*} [Category* D] [Preadditive D]
    {U U' V E : D} (e : U' ≅ U) (p : U' ⟶ V) (f : V ⟶ E) :
    p ≫ f = 0 ↔ (e.inv ≫ p) ≫ f = 0 := by
  constructor
  · intro h
    rw [Category.assoc, h, comp_zero]
  · intro h
    apply (cancel_epi e.inv).mp
    rw [← Category.assoc, h, comp_zero]

/-- Both SAME original counit directions identify the original-Y and QY zero kernels. -/
theorem original_target_kernel (F : Arrow C) (E : HomotopyCategory C) (f : cofiberHo g Z hZ F ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    cofiberRestriction g Z hZ F E f = 0 ↔ originalCofiberRestriction g Z hZ F E f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  exact zero_precomp_iso (targetCounitIso g Z hZ F) (targetArrow g Z hZ F) f

/-- The actual ordinary-suspension connecting image equals the ORIGINAL target-Y zero kernel at every Ho target. -/
theorem exact_at_cofiber_original (F : Arrow C) (E : HomotopyCategory C) (f : cofiberHo g Z hZ F ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E, connecting g Z hZ F E h = f) ↔
      originalCofiberRestriction g Z hZ F E f = 0 :=
  (exact_at_cofiber g Z hZ F E f).trans (original_target_kernel g Z hZ F E f)

/-- The original input Arrow induces the complete original-Y to original-X additive restriction. -/
def inputRestriction (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E ((toHomotopyCategory C).map F.hom)

/-- The original cofiber image is exactly the original-X zero kernel at the stated original fibrant target. -/
theorem exact_at_target_fibrant (F : Arrow C) (E : C) [IsFibrant E]
    (f : (toHomotopyCategory C).obj F.right ⟶ (toHomotopyCategory C).obj E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : cofiberHo g Z hZ F ⟶ (toHomotopyCategory C).obj E,
      originalCofiberRestriction g Z hZ F ((toHomotopyCategory C).obj E) h = f) ↔
      inputRestriction g F ((toHomotopyCategory C).obj E) f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  have hpre {A B : HomotopyCategory C} (p : A ⟶ B)
      (a : B ⟶ (toHomotopyCategory C).obj E) :
      (Preadditive.leftComp ((toHomotopyCategory C).obj E) p) a = p ≫ a := rfl
  have ht := GeneratedOrdinaryPuppeLoopSequence.exact_at_target_original g Z hZ F E f
  rw [OrdinaryStableHoPreadditive.nullHom_eq_zero g F.left E] at ht
  unfold originalCofiberRestriction originalTargetArrow targetArrow targetCounitIso cofiberHo inputRestriction
  simp only [hpre, id_eq]
  exact ht

/-- The SAME actual original R unit transports the original target/source exact group position to EVERY Ho target. -/
theorem exact_at_target_original (F : Arrow C) (E : HomotopyCategory C)
    (f : (toHomotopyCategory C).obj F.right ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : cofiberHo g Z hZ F ⟶ E, originalCofiberRestriction g Z hZ F E h = f) ↔
      inputRestriction g F E f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  let X : C := (toHomotopyCategory C).objPreimage E
  let r : (toHomotopyCategory C).obj X ⟶
      (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app X)
  let : IsIso r := Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
    (GeneratedFunctorialReplacements.unit_weak g X)
  let : IsFibrant ((GeneratedFunctorialReplacements.R g).obj X) :=
    GeneratedFunctorialReplacements.R_isFibrant g X
  let e : E ≅ (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    ((toHomotopyCategory C).objObjPreimageIso E).symm ≪≫ asIso r
  have he : ∀ h : (toHomotopyCategory C).obj F.right ⟶
      (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X),
      (∃ t : cofiberHo g Z hZ F ⟶
          (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X),
        originalTargetArrow g Z hZ F ≫ t = h) ↔ (toHomotopyCategory C).map F.hom ≫ h = 0 := by
    intro h
    exact exact_at_target_fibrant g Z hZ F ((GeneratedFunctorialReplacements.R g).obj X) h
  exact Preadditive.exact_target_iso ((toHomotopyCategory C).map F.hom)
    (originalTargetArrow g Z hZ F) e he f

/-- The original ordinary suspension of the source Arrow gives the preceding additive restriction. -/
def suspensionRestriction (F : Arrow C) (E : HomotopyCategory C) := by
  letI := OrdinaryStableHoPreadditive.preadditive g
  exact Preadditive.leftComp E ((Σ).map ((toHomotopyCategory C).map F.hom))

/-- The opaque cofiber presentation is the SAME actual original Q-cofiber object in Ho. -/
def cofiberPresentationIso (F : Arrow C) : cofiberHo g Z hZ F ≅
    (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).obj F) := by
  unfold cofiberHo
  exact Iso.refl _

/-- At a fibrant target the SAME original ordinary Hom functions give the connecting zero kernel. -/
theorem exact_at_suspension_fibrant (F : Arrow C) (E : C) [IsFibrant E]
    (f : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ (toHomotopyCategory C).obj E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : (Σ).obj ((toHomotopyCategory C).obj F.right) ⟶ (toHomotopyCategory C).obj E,
      suspensionRestriction g F ((toHomotopyCategory C).obj E) h = f) ↔
      connecting g Z hZ F ((toHomotopyCategory C).obj E) f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  have hpre {A B : HomotopyCategory C} (p : A ⟶ B)
      (a : B ⟶ (toHomotopyCategory C).obj E) :
      (Preadditive.leftComp ((toHomotopyCategory C).obj E) p) a = p ≫ a := rfl
  have ht := GeneratedOrdinaryPuppeLoopSequence.exact_at_loop_source g Z hZ F E
    ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E) f)
  rw [OrdinaryStableHoPreadditive.nullHom_eq_zero g _ E] at ht
  have hConnecting : connecting g Z hZ F ((toHomotopyCategory C).obj E) f =
      (cofiberPresentationIso g Z hZ F).hom ≫ GeneratedOrdinaryPuppeLoopSequence.connecting g Z hZ F E
        ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E) f) := by
    unfold connecting boundaryArrow OrdinaryStablePuppeGroups.boundaryArrow framingSourceIso
      GeneratedOrdinaryPuppeLoopSequence.connecting
    unfold cofiberPresentationIso cofiberHo suspendedHoSource suspendedSource
    simp only [hpre, id_eq,
      GeneratedOrdinarySuspensionHom.homEquiv_symm_apply,
      Equiv.symm_apply_apply, Iso.refl_hom, Category.id_comp]
    exact Category.assoc _ _ _
  constructor
  · rintro ⟨h, hh⟩
    have hz : GeneratedOrdinaryPuppeLoopSequence.connecting g Z hZ F E
        ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E) f) = 0 := by
      apply ht.mp
      refine ⟨(adjOrd).homEquiv ((toHomotopyCategory C).obj F.right) ((toHomotopyCategory C).obj E) h, ?_⟩
      have hn := (adjOrd).homEquiv_naturality_left ((toHomotopyCategory C).map F.hom) h
      exact hn.symm.trans (congrArg
        ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E)) hh)
    rw [hConnecting, hz, comp_zero]
  · intro hf
    have hz : GeneratedOrdinaryPuppeLoopSequence.connecting g Z hZ F E
        ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E) f) = 0 := by
      apply (cancel_epi (cofiberPresentationIso g Z hZ F).hom).mp
      rw [comp_zero]
      exact hConnecting.symm.trans hf
    obtain ⟨h, hh⟩ := ht.mpr hz
    refine ⟨((adjOrd).homEquiv ((toHomotopyCategory C).obj F.right)
      ((toHomotopyCategory C).obj E)).symm h, ?_⟩
    apply ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E)).injective
    change (adjOrd).homEquiv ((toHomotopyCategory C).obj F.left) ((toHomotopyCategory C).obj E)
        ((Σ).map ((toHomotopyCategory C).map F.hom) ≫
          ((adjOrd).homEquiv ((toHomotopyCategory C).obj F.right) ((toHomotopyCategory C).obj E)).symm h) = _
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
    exact hh

/-- The original R unit gives the SAME connecting zero-kernel group position for EVERY Ho target. -/
theorem exact_at_suspension (F : Arrow C) (E : HomotopyCategory C)
    (f : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶ E) :
    letI := OrdinaryStableHoPreadditive.preadditive g
    (∃ h : (Σ).obj ((toHomotopyCategory C).obj F.right) ⟶ E, suspensionRestriction g F E h = f) ↔
      connecting g Z hZ F E f = 0 := by
  let := OrdinaryStableHoPreadditive.preadditive g
  let : (toHomotopyCategory C).EssSurj := Localization.essSurj (toHomotopyCategory C) (weakEquivalences C)
  let X : C := (toHomotopyCategory C).objPreimage E
  let r : (toHomotopyCategory C).obj X ⟶
      (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.unit g).app X)
  let : IsIso r := Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
    (GeneratedFunctorialReplacements.unit_weak g X)
  let : IsFibrant ((GeneratedFunctorialReplacements.R g).obj X) :=
    GeneratedFunctorialReplacements.R_isFibrant g X
  let e : E ≅ (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X) :=
    ((toHomotopyCategory C).objObjPreimageIso E).symm ≪≫ asIso r
  have he : ∀ h : (Σ).obj ((toHomotopyCategory C).obj F.left) ⟶
      (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X),
      (∃ t : (Σ).obj ((toHomotopyCategory C).obj F.right) ⟶
          (toHomotopyCategory C).obj ((GeneratedFunctorialReplacements.R g).obj X),
        (Σ).map ((toHomotopyCategory C).map F.hom) ≫ t = h) ↔ boundaryArrow g Z hZ F ≫ h = 0 := by
    intro h
    exact exact_at_suspension_fibrant g Z hZ F ((GeneratedFunctorialReplacements.R g).obj X) h
  exact Preadditive.exact_target_iso (boundaryArrow g Z hZ F)
    ((Σ).map ((toHomotopyCategory C).map F.hom)) e he f

end HomotopicalAlgebra.OrdinaryStablePuppeConnecting
