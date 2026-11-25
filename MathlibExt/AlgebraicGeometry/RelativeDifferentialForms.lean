/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialTensor
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Actual differential forms relative to an arbitrary scheme base

The coefficient presheaf is the native left Kan extension of O_T along the
actual inverse-image functor on opens. Its map to O_Y is the native Kan
extension of the scheme's structure map. Sectionwise Kähler differentials,
exterior powers and sheafification are actual native constructions. The
universal derivation annihilates every pulled-back base section.

Sources: Mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679,
ModuleCat/Differentials/Presheaf and Functor/KanExtension (Joël Riou, 2024),
Apache 2.0. General sheaf differentials and de Rham producers are complete in
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Topology/Sheaves/Modules/Differentials and
AlgebraicGeometry/DeRham/DifferentialGradedAlgebra/Basic, Apache 2.0.
Modification: compose the native Kan and sectionwise universal constructors,
retaining the literal relative base map. One-forms use the Kähler module
itself and two-forms its actual exterior square.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section


namespace MathlibExt.AlgebraicGeometry.RelativeDifferentialForms

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry Opposite
open TopologicalSpace PresheafOfModulesOfCommRing
open LineBundleTaskContracts AlgebraicLineBundleFamilies
open NativeTensorComparisons

variable {Y T : Scheme.{0}} (pi : Y ⟶ T)

local instance (U : Y.Opensᵒᵖ) : CommRing (Y.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (Y.presheaf.obj U))

abbrev inverseImageFunctor : T.Opensᵒᵖ ⥤ Y.Opensᵒᵖ := (Opens.map pi.base).op

abbrev pulledRing : Y.Opensᵒᵖ ⥤ CommRingCat.{0} :=
  (inverseImageFunctor pi).leftKanExtension T.presheaf

def baseMap : pulledRing pi ⟶ Y.presheaf :=
  (pulledRing pi).descOfIsLeftKanExtension
    ((inverseImageFunctor pi).leftKanExtensionUnit T.presheaf) Y.presheaf pi.c

theorem baseMap_factor (U : T.Opens) (a : Γ(T, U)) :
    (baseMap pi).app ((inverseImageFunctor pi).obj (op U))
      (((inverseImageFunctor pi).leftKanExtensionUnit T.presheaf).app (op U) a) = pi.app U a := by
  have h := (pulledRing pi).descOfIsLeftKanExtension_fac_app
    ((inverseImageFunctor pi).leftKanExtensionUnit T.presheaf) Y.presheaf pi.c (op U)
  exact congrArg (fun f : Γ(T, U) ⟶ Γ(Y, pi ⁻¹ᵁ U) ↦ f.hom a) h

abbrev differentials : PresheafOfModulesOfCommRing Y.presheaf :=
  DifferentialsConstruction.relativeDifferentials' (baseMap pi)

def relativeDerivation : (differentials pi).Derivation pi.c where
  d := (DifferentialsConstruction.derivation' (baseMap pi)).d
  d_mul := (DifferentialsConstruction.derivation' (baseMap pi)).d_mul
  d_map := (DifferentialsConstruction.derivation' (baseMap pi)).d_map
  d_app {U} a := by
    change (DifferentialsConstruction.derivation' (baseMap pi)).d ((pi.app U.unop).hom a) = 0
    rw [← baseMap_factor pi U.unop a]
    exact (DifferentialsConstruction.derivation' (baseMap pi)).d_app _

abbrev formsPresheaf (p : ℕ) : PresheafOfModulesOfCommRing Y.presheaf :=
  if p = 1 then differentials pi else PresheafOfModules.extPow p (differentials pi)

def forms (p : ℕ) : Y.Modules := (sheafifyModules Y).obj (formsPresheaf pi p)

/-- The native universal differential followed by the actual sheafification unit. -/
def d0 : ((forgetModules Y).obj (forms pi 1)).Derivation pi.c :=
  (relativeDerivation pi).postcomp ((moduleAdjunction Y).unit.app (differentials pi))

theorem d0_base_section (U : T.Opens) (V : Y.Opens) (h : V ≤ pi ⁻¹ᵁ U) (a : Γ(T, U)) :
    (d0 pi).d ((pi.appLE U V h).hom a) = 0 := by
  change (d0 pi).d ((Y.presheaf.map (homOfLE h).op).hom ((pi.app U).hom a)) = 0
  have hm := (d0 pi).d_map (homOfLE h).op ((pi.app U).hom a)
  have ha := (d0 pi).d_app (X := op U) a
  change (d0 pi).d ((pi.app U).hom a) = 0 at ha
  exact hm.trans (by rw [ha]; exact map_zero _)

def lambdaOnOpen (lambda : Γ(T, ⊤)) (U : Y.Opens) : Γ(Y, U) :=
  (pi.appLE ⊤ U (by intro x hx; trivial)).hom lambda

@[simp] theorem d0_lambda (lambda : Γ(T, ⊤)) (U : Y.Opens) :
    (d0 pi).d (lambdaOnOpen pi lambda U) = 0 :=
  d0_base_section pi ⊤ U _ lambda

def wedgeElement (U : Y.Opensᵒᵖ) (a b : (differentials pi).obj U) :
    (formsPresheaf pi 2).obj U :=
  AlgebraicDifferentialTensor.exteriorMultiply 1 1
    ((exteriorPower.oneEquiv (Y.ringCatSheaf.obj.obj U)
      (PresheafOfModules.obj (differentials pi) U)).symm a)
    ((exteriorPower.oneEquiv (Y.ringCatSheaf.obj.obj U)
      (PresheafOfModules.obj (differentials pi) U)).symm b)

def presheafWedge :
    formsPresheaf pi 1 ⊗ formsPresheaf pi 1 ⟶ formsPresheaf pi 2 :=
  PresheafOfModules.tensorMk
    (fun U x y ↦ wedgeElement pi U x y)
    (by
      intro U a b c
      apply (PresheafOfModules.extPowSections 2 (differentials pi) U).injective
      simp only [map_add]
      apply Subtype.ext
      simp [PresheafOfModules.extPowSections, wedgeElement,
        AlgebraicDifferentialTensor.exteriorMultiply, map_add, add_mul]
      rfl)
    (by
      intro U r a b
      apply (PresheafOfModules.extPowSections 2 (differentials pi) U).injective
      simp only [map_smul]
      apply Subtype.ext
      simp [PresheafOfModules.extPowSections, wedgeElement,
        AlgebraicDifferentialTensor.exteriorMultiply, map_smul]
      rfl)
    (by
      intro U a b c
      apply (PresheafOfModules.extPowSections 2 (differentials pi) U).injective
      simp only [map_add]
      apply Subtype.ext
      simp [PresheafOfModules.extPowSections, wedgeElement,
        AlgebraicDifferentialTensor.exteriorMultiply, map_add, mul_add]
      rfl)
    (by
      intro U r a b
      apply (PresheafOfModules.extPowSections 2 (differentials pi) U).injective
      simp only [map_smul]
      apply Subtype.ext
      simp [PresheafOfModules.extPowSections, wedgeElement,
        AlgebraicDifferentialTensor.exteriorMultiply, map_smul]
      rfl)
    (by
      intro U V f a b
      apply Subtype.ext
      change (PresheafOfModules.extPowRestrict 2 (differentials pi) f
        (wedgeElement pi U a b) : ExteriorAlgebra (Y.ringCatSheaf.obj.obj V)
          ((differentials pi).obj V)) = _
      rw [PresheafOfModules.extPowRestrict_coe]
      dsimp only [wedgeElement, AlgebraicDifferentialTensor.exteriorMultiply]
      simp only [exteriorPower.oneEquiv_symm_apply]
      rw [map_mul]
      congr 1 <;> exact ExteriorAlgebra.mapₛₗ_ιMulti
        (Y.ringCatSheaf.obj.map f).hom ((differentials pi).restrictₛₗ f) 1 _)

def wedge : moduleTensor Y (forms pi 1) (forms pi 1) ⟶ forms pi 2 :=
  (asIso (pairComparison Y (formsPresheaf pi 1) (formsPresheaf pi 1))).inv ≫
    (sheafifyModules Y).map (presheafWedge pi)

end MathlibExt.AlgebraicGeometry.RelativeDifferentialForms
