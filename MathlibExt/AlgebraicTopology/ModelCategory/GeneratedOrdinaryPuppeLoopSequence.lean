/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinarySuspensionHom

/-!
# Original Puppe connecting maps through the actual ordinary loops

The connecting function is the unchanged Q-cofiber boundary followed by
the earned inverse ordinary suspension/loop Hom function. Every source
Arrow and target map is retained. The loop-source and cofiber image/kernel
identities follow from the actual third and second chosen Puppe positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinaryPuppeLoopSequence

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The target is the actual original ordinary loop functor from the same framing data. -/
abbrev loopHom (X E : C) :=
  (toHomotopyCategory C).obj X ⟶
    (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
      ((toHomotopyCategory C).obj E)

/-- The cofiber Hom term retains the original whole Q-cofiber functor. -/
abbrev cofiberHom (F : Arrow C) (E : C) :=
  (toHomotopyCategory C).obj ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).obj F) ⟶
    (toHomotopyCategory C).obj E

/-- The actual connecting function uses the original boundary and inverse ordinary Hom map. -/
def connecting (F : Arrow C) (E : C) : loopHom g F.left E → cofiberHom g Z hZ F E :=
  fun f => (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.boundary g Z hZ).app F) ≫
    (GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E).symm f

/-- Every entire source Arrow square retains both original connecting-map functions. -/
theorem connecting_source {F G : Arrow C} (a : F ⟶ G) (E : C) (f : loopHom g G.left E) :
    connecting g Z hZ F E ((toHomotopyCategory C).map a.left ≫ f) =
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).map a) ≫
        connecting g Z hZ G E f := by
  have hBoundary :
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).map a) ≫
          (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.boundary g Z hZ).app G) =
        (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.boundary g Z hZ).app F) ≫
          (toHomotopyCategory C).map ((GeneratedOrdinarySuspensionHom.coneSuspension g Z hZ).map a.left) :=
    ((toHomotopyCategory C).map_comp _ _).symm.trans
      (((toHomotopyCategory C).congr_map ((GeneratedOrdinaryPuppe.boundary g Z hZ).naturality a)).trans
        ((toHomotopyCategory C).map_comp _ _))
  unfold connecting
  rw [GeneratedOrdinarySuspensionHom.homEquiv_symm_source, ← Category.assoc,
    ← hBoundary, Category.assoc]

/-- Every full target map retains the actual ordinary loop map and original postcomposition. -/
theorem connecting_target (F : Arrow C) {E E' : C} (a : E ⟶ E') (f : loopHom g F.left E) :
    connecting g Z hZ F E'
        (f ≫ (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).map
          ((toHomotopyCategory C).map a)) =
      connecting g Z hZ F E f ≫ (toHomotopyCategory C).map a := by
  unfold connecting
  rw [GeneratedOrdinarySuspensionHom.homEquiv_symm_target]
  exact (Category.assoc _ _ _).symm

/-- The original third Puppe position becomes the actual ordinary-loop connecting null kernel. -/
theorem exact_at_loop_source (F : Arrow C) (E : C) [IsFibrant E] (f : loopHom g F.left E) :
    (∃ h : loopHom g F.right E, (toHomotopyCategory C).map F.hom ≫ h = f) ↔
      connecting g Z hZ F E f =
        OrdinaryHoCofiberKernel.nullHom ((GeneratedOrdinaryPuppe.termFunctor g Z hZ 2).obj F) E := by
  let _ : IsCofibrant ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant g F.right
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion g Z hZ).app
      ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration g Z hZ _)
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion g Z hZ).app
      ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).right) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration g Z hZ _)
  have hOriginal := OrdinaryHoChosenPuppeHomSequence.third_exact Z hZ
    (GeneratedOrdinaryCone.cone g Z hZ) (GeneratedOrdinaryCone.inclusion g Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone g Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit g Z hZ) ((GeneratedOrdinaryCofiber.replacementArrow g).obj F) E
    (GeneratedOrdinaryCone.toZero_cone_weak g Z hZ _)
    ((GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E).symm f)
  constructor
  · rintro ⟨h, hh⟩
    apply hOriginal.mp
    refine ⟨(GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.right E).symm h, ?_⟩
    exact (GeneratedOrdinarySuspensionHom.homEquiv_symm_source g Z hZ F.hom E h).symm.trans
      (congrArg (GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E).symm hh)
  · intro hf
    obtain ⟨h, hh⟩ := hOriginal.mpr hf
    refine ⟨GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.right E h, ?_⟩
    exact (GeneratedOrdinarySuspensionHom.homEquiv_source g Z hZ F.hom E h).symm.trans
      ((congrArg (GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E) hh).trans
        (Equiv.apply_symm_apply _ f))

/-- The original second Puppe position gives the actual connecting image and original Q-target null kernel. -/
theorem exact_at_cofiber (F : Arrow C) (E : C) [IsFibrant E] (f : cofiberHom g Z hZ F E) :
    (∃ h : loopHom g F.left E, connecting g Z hZ F E h = f) ↔
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) ≫ f =
        OrdinaryHoCofiberKernel.nullHom
          ((GeneratedFunctorialReplacements.Q g).obj F.right) E := by
  let _ : IsCofibrant ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant g F.right
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion g Z hZ).app
      ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration g Z hZ _)
  have hOriginal := OrdinaryHoChosenPuppe.second_exact Z hZ
    (GeneratedOrdinaryCone.cone g Z hZ) (GeneratedOrdinaryCone.inclusion g Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone g Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit g Z hZ) ((GeneratedOrdinaryCofiber.replacementArrow g).obj F) E f
  constructor
  · rintro ⟨h, hh⟩
    exact hOriginal.mp ⟨(GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E).symm h, hh⟩
  · intro hf
    obtain ⟨h, hh⟩ := hOriginal.mpr hf
    refine ⟨GeneratedOrdinarySuspensionHom.homEquiv g Z hZ F.left E h, ?_⟩
    unfold connecting
    rw [Equiv.symm_apply_apply]
    exact hh

/-- The original full Q counit is a natural isomorphism on the same canonical Ho. -/
private def qCounitHoIso : GeneratedFunctorialReplacements.Q g ⋙ toHomotopyCategory C ≅
    toHomotopyCategory C :=
  NatIso.ofComponents (PointedFramingAction.qHomotopyIso (GeneratedFunctorialReplacements.fromGeneration g))
    (fun {X Y} f => by
      change (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.Q g).map f) ≫
          (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app Y) =
        (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.counit g).app X) ≫
          (toHomotopyCategory C).map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((GeneratedFunctorialReplacements.counit g).naturality f))

/-- The original Q-target inclusion is transported by the actual q_Y inverse on every original Arrow. -/
def targetInclusion : Arrow.rightFunc ⋙ toHomotopyCategory C ⟶
    GeneratedOrdinaryPuppe.termFunctor g Z hZ 2 ⋙ toHomotopyCategory C :=
  Functor.whiskerLeft Arrow.rightFunc (qCounitHoIso g).inv ≫
    Functor.whiskerRight (GeneratedOrdinaryPuppe.step g Z hZ 1) (toHomotopyCategory C)

omit [HasZeroObject C] [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C] in
/-- The full original q_Y forward function recovers the unchanged actual cofiber target leg. -/
private theorem targetInclusion_q (F : Arrow C) :
    (qCounitHoIso g).hom.app F.right ≫ (targetInclusion g Z hZ).app F =
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) := by
  change (qCounitHoIso g).hom.app F.right ≫
      ((qCounitHoIso g).inv.app F.right ≫
        (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F))
      (Iso.hom_inv_id_app (qCounitHoIso g) F.right)).trans (Category.id_comp _))

omit [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C] in
/-- The same actual Q counit retains the original ordinary null class. -/
private theorem qCounit_null (X E : C) :
    (qCounitHoIso g).hom.app X ≫ OrdinaryHoCofiberKernel.nullHom X E =
      OrdinaryHoCofiberKernel.nullHom ((GeneratedFunctorialReplacements.Q g).obj X) E :=
  OrdinaryHoCofiberKernel.precomp_nullHom ((GeneratedFunctorialReplacements.counit g).app X)

omit [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C] in
/-- The actual original-target null kernel is exactly the unchanged Q-target null kernel. -/
theorem targetInclusion_null_iff (F : Arrow C) (E : C) (f : cofiberHom g Z hZ F E) :
    (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) ≫ f =
        OrdinaryHoCofiberKernel.nullHom ((GeneratedFunctorialReplacements.Q g).obj F.right) E ↔
      (targetInclusion g Z hZ).app F ≫ f = OrdinaryHoCofiberKernel.nullHom F.right E := by
  constructor
  · intro hf
    apply (cancel_epi ((qCounitHoIso g).hom.app F.right)).mp
    calc
      (qCounitHoIso g).hom.app F.right ≫ ((targetInclusion g Z hZ).app F ≫ f) =
          ((qCounitHoIso g).hom.app F.right ≫ (targetInclusion g Z hZ).app F) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) ≫ f :=
        congrArg (fun a => a ≫ f) (targetInclusion_q g Z hZ F)
      _ = OrdinaryHoCofiberKernel.nullHom ((GeneratedFunctorialReplacements.Q g).obj F.right) E := hf
      _ = (qCounitHoIso g).hom.app F.right ≫ OrdinaryHoCofiberKernel.nullHom F.right E :=
        (qCounit_null g F.right E).symm
  · intro hf
    calc
      (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) ≫ f =
          ((qCounitHoIso g).hom.app F.right ≫ (targetInclusion g Z hZ).app F) ≫ f :=
        congrArg (fun a => a ≫ f) (targetInclusion_q g Z hZ F).symm
      _ = (qCounitHoIso g).hom.app F.right ≫ ((targetInclusion g Z hZ).app F ≫ f) := Category.assoc _ _ _
      _ = (qCounitHoIso g).hom.app F.right ≫ OrdinaryHoCofiberKernel.nullHom F.right E :=
        congrArg (fun a => (qCounitHoIso g).hom.app F.right ≫ a) hf
      _ = OrdinaryHoCofiberKernel.nullHom ((GeneratedFunctorialReplacements.Q g).obj F.right) E :=
        qCounit_null g F.right E

/-- The connecting image is the null kernel of the actual original-target cofiber restriction. -/
theorem exact_at_cofiber_original (F : Arrow C) (E : C) [IsFibrant E] (f : cofiberHom g Z hZ F E) :
    (∃ h : loopHom g F.left E, connecting g Z hZ F E h = f) ↔
      (targetInclusion g Z hZ).app F ≫ f = OrdinaryHoCofiberKernel.nullHom F.right E :=
  (exact_at_cofiber g Z hZ F E f).trans (targetInclusion_null_iff g Z hZ F E f)

omit [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C] in
/-- The original cofiber restriction image is exactly the original source-map null kernel. -/
theorem exact_at_target_original (F : Arrow C) (E : C) [IsFibrant E]
    (f : (toHomotopyCategory C).obj F.right ⟶ (toHomotopyCategory C).obj E) :
    (∃ h : cofiberHom g Z hZ F E, (targetInclusion g Z hZ).app F ≫ h = f) ↔
      (toHomotopyCategory C).map F.hom ≫ f = OrdinaryHoCofiberKernel.nullHom F.left E := by
  let _ : IsCofibrant ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant g F.left
  let _ : IsCofibrant ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant g F.right
  let _ : Cofibration ((GeneratedOrdinaryCone.inclusion g Z hZ).app
      ((GeneratedOrdinaryCofiber.replacementArrow g).obj F).left) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration g Z hZ _)
  have hOriginal := OrdinaryHoChosenPuppe.first_exact Z hZ
    (GeneratedOrdinaryCone.cone g Z hZ) (GeneratedOrdinaryCone.inclusion g Z hZ)
    (GeneratedOrdinaryCone.cofiberCocone g Z hZ)
    (GeneratedOrdinaryCone.cofiberIsColimit g Z hZ) ((GeneratedOrdinaryCofiber.replacementArrow g).obj F) E
    (GeneratedOrdinaryCone.toZero_cone_weak g Z hZ _)
    ((qCounitHoIso g).hom.app F.right ≫ f)
  have hImage :
      (∃ h : cofiberHom g Z hZ F E,
        (toHomotopyCategory C).map ((GeneratedOrdinaryPuppe.step g Z hZ 1).app F) ≫ h =
          (qCounitHoIso g).hom.app F.right ≫ f) ↔
      (∃ h : cofiberHom g Z hZ F E, (targetInclusion g Z hZ).app F ≫ h = f) := by
    constructor
    · rintro ⟨h, hh⟩
      refine ⟨h, (cancel_epi ((qCounitHoIso g).hom.app F.right)).mp ?_⟩
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ h) (targetInclusion_q g Z hZ F))).trans hh
    · rintro ⟨h, hh⟩
      refine ⟨h, ?_⟩
      exact ((congrArg (fun a => a ≫ h) (targetInclusion_q g Z hZ F).symm).trans
        (Category.assoc _ _ _)).trans
          (congrArg (fun a => (qCounitHoIso g).hom.app F.right ≫ a) hh)
  have hSource :
      (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.Q g).map F.hom) ≫
          (qCounitHoIso g).hom.app F.right =
        (qCounitHoIso g).hom.app F.left ≫ (toHomotopyCategory C).map F.hom :=
    (qCounitHoIso g).hom.naturality F.hom
  have hKernelMap :
      (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.Q g).map F.hom) ≫
          ((qCounitHoIso g).hom.app F.right ≫ f) =
        (qCounitHoIso g).hom.app F.left ≫ ((toHomotopyCategory C).map F.hom ≫ f) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ f) hSource).trans (Category.assoc _ _ _))
  have hKernel :
      (toHomotopyCategory C).map ((GeneratedFunctorialReplacements.Q g).map F.hom) ≫
          ((qCounitHoIso g).hom.app F.right ≫ f) =
        OrdinaryHoCofiberKernel.nullHom ((GeneratedFunctorialReplacements.Q g).obj F.left) E ↔
      (toHomotopyCategory C).map F.hom ≫ f = OrdinaryHoCofiberKernel.nullHom F.left E := by
    constructor
    · intro hf
      apply (cancel_epi ((qCounitHoIso g).hom.app F.left)).mp
      exact hKernelMap.symm.trans (hf.trans (qCounit_null g F.left E).symm)
    · intro hf
      exact hKernelMap.trans
        ((congrArg (fun a => (qCounitHoIso g).hom.app F.left ≫ a) hf).trans (qCounit_null g F.left E))
  exact hImage.symm.trans (hOriginal.trans hKernel)

end HomotopicalAlgebra.GeneratedOrdinaryPuppeLoopSequence
