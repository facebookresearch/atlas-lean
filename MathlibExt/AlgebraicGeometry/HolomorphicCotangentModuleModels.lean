/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicHolomorphicModuleModels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Holomorphic cotangent modules on actual complex manifolds

Forms are actual continuous alternating complex tangent covectors, whose
native chart pullbacks are holomorphic. Their O-action and restriction are
pointwise. The tensor product is the native presheaf tensor product followed
by native sheafification. Neither a cotangent object nor a tensor operation
is selected independently of those sections.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace Set
open KahlerClassGeometry ManifoldDifferentialForms HolomorphicCoefficientSheaves
open HarmonicHolomorphicModuleModels
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]

/-- Actual tangent covectors carry the literal holomorphic-function scalar action. -/
instance formHolomorphicModule (U : Opens M) (p : ℕ) :
    Module (HolomorphicScalars (n := n) U) (RoughForm ℂ (Coordinates n) M U p) :=
  Module.compHom (RoughForm ℂ (Coordinates n) M U p)
    (holomorphicAlgebra (Coordinates n) M U).val.toRingHom

/-- Ordinary local multiplication, restriction and gluing for these same holomorphic covectors. -/
class CotangentSectionCalculus : Prop where
  mul : ∀ (U : Opens M) (p : ℕ) (f : HolomorphicScalars (n := n) U)
    (α : RoughForm ℂ (Coordinates n) M U p), IsSmooth ℂ (Coordinates n) M α →
      IsSmooth ℂ (Coordinates n) M (f • α)
  restriction : ∀ (U V : Opens M) (a : V ≤ U) (p : ℕ)
    (α : RoughForm ℂ (Coordinates n) M U p), IsSmooth ℂ (Coordinates n) M α →
      IsSmooth ℂ (Coordinates n) M (fun x : V => α ⟨x.val, a x.property⟩)

variable [CotangentSectionCalculus (n := n) (M := M)]

/-- The cotangent p-forms are the actual O-module of holomorphic tangent covectors. -/
def holomorphicFormModule (U : Opens M) (p : ℕ) :
    Submodule (HolomorphicScalars (n := n) U) (RoughForm ℂ (Coordinates n) M U p) where
  carrier := {α | IsSmooth ℂ (Coordinates n) M α}
  zero_mem' := (smoothForms ℂ (Coordinates n) M U p).zero_mem
  add_mem' ha hb := (smoothForms ℂ (Coordinates n) M U p).add_mem ha hb
  smul_mem' f α hα := CotangentSectionCalculus.mul (n := n) (M := M) U p f α hα

/-- The actual function-times-covector action, with the coefficient and exterior degree explicit. -/
def scaleHolomorphicForm {U : Opens M} {p : ℕ} (f : HolomorphicScalars (n := n) U)
    (α : holomorphicFormModule (n := n) (M := M) U p) :
    holomorphicFormModule (n := n) (M := M) U p :=
  ⟨fun y => f.val y • α.val y,
    CotangentSectionCalculus.mul (n := n) (M := M) U p f α.val α.property⟩

/-- Actual restriction, semilinear over the actual holomorphic function restriction. -/
def formRestriction {U V : Opens M} (a : V ≤ U) (p : ℕ) :
    holomorphicFormModule (n := n) (M := M) U p →ₛₗ[(restriction (Coordinates n) M a).toRingHom]
      holomorphicFormModule (n := n) (M := M) V p where
  toFun α := ⟨fun x => α.val ⟨x.val, a x.property⟩,
    CotangentSectionCalculus.restriction (n := n) (M := M) U V a p α.val α.property⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- O-modules of actual covectors in every exterior degree, with all native restriction maps. -/
def formModulePresheaf (p : ℕ) : PresheafOfModules.{0} (ringPresheaf (Coordinates n) M) where
  obj U := ModuleCat.of (HolomorphicScalars (n := n) U.unop) (holomorphicFormModule (n := n) (M := M) U.unop p)
  map {U V} a := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((ringPresheaf (Coordinates n) M).map a).hom).obj
      (ModuleCat.of (HolomorphicScalars (n := n) V.unop) (holomorphicFormModule (n := n) (M := M) V.unop p))) {
    toFun := formRestriction (n := n) (M := M) a.unop.le p
    map_add' := (formRestriction (n := n) (M := M) a.unop.le p).map_add
    map_smul' := by intro f α; apply Subtype.ext; rfl }
  map_id U := by apply ModuleCat.hom_ext; ext α; rfl
  map_comp a b := by apply ModuleCat.hom_ext; ext α; rfl

/-- The sheaf condition concerns the actual covector presheaf, without any Higgs conclusion. -/
class CotangentSheafCondition : Prop where
  isSheaf : ∀ p : ℕ, Presheaf.IsSheaf (Opens.grothendieckTopology M)
    (formModulePresheaf (n := n) (M := M) p).presheaf

variable [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSheafCondition (n := n) (M := M)]

/-- The actual sheaf Omega^p of holomorphic complex cotangent forms. -/
def holomorphicOmega (p : ℕ) : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) :=
  ⟨formModulePresheaf (n := n) (M := M) p, CotangentSheafCondition.isSheaf (n := n) (M := M) p⟩

/-- Every coefficient is the actual commutative holomorphic ring. -/
instance holomorphicStructureRingComm (U : (Opens M)ᵒᵖ) :
    CommRing ((holomorphicStructureRing (n := n) (M := M)).obj.obj U) :=
  inferInstanceAs (CommRing (HolomorphicScalars (n := n) U.unop))

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The same actual holomorphic coefficients, retaining their native commutative-ring packaging. -/
def holomorphicCommutativePresheaf : (Opens M)ᵒᵖ ⥤ CommRingCat.{0} :=
  coefficientPresheaf (Coordinates n) M ⋙ forget₂ (CommAlgCat.{0} ℂ) CommRingCat.{0}

/-- The actual termwise native tensor of the underlying holomorphic module presheaves. -/
def holomorphicPresheafTensor
    (E F : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))) :
    PresheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)).obj :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj
    (R := holomorphicCommutativePresheaf (n := n) (M := M)) E.val F.val

/-- The actual tensor of O-modules is native tensor/sheafification on the same holomorphic ring. -/
def holomorphicTensor
    (E F : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))) :
    SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M)) :=
  (PresheafOfModules.sheafification (𝟙 (holomorphicStructureRing (n := n) (M := M)).obj)).obj
    (holomorphicPresheafTensor E F)

/-- The tensor section is the actual pure tensor followed by the native sheafification unit. -/
def holomorphicTensorSection
    (E F : SheafOfModules.{0} (holomorphicStructureRing (n := n) (M := M))) (U : Opens M)
    (e : E.val.obj (op U)) (α : F.val.obj (op U)) :
    (holomorphicTensor E F).val.obj (op U) :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (holomorphicStructureRing (n := n) (M := M)).obj)).unit.app (holomorphicPresheafTensor E F)).app (op U)).hom
      (e ⊗ₜ[HolomorphicScalars (n := n) U] α)

end MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
