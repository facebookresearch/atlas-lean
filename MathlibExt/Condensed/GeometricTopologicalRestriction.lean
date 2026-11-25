/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import MathlibExt.Condensed.AdicSolidGenerators

/-!
# Actual continuous change of geometric condensed coefficients

A continuous ring map induces the displayed map C(S,A) -> C(S,B) on
every compact Hausdorff test. Restriction retains every section and
changes its scalar action by this map. Scalar extension is the native
chosen left adjoint of that actual restriction, not an independently
chosen functor.

The derived restriction uses its fixed cochain source. Analytic and
adic reflection comparison maps are uniquely induced by their actual
units. Preservation of the relevant local conditions remains explicit.

References: Anschuetz--Mann, arXiv:2403.01951v2, Sections 2.1--2.2;
Clausen--Scholze, Lectures on Condensed Mathematics, Lectures II and V.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.GeometricTopologicalRestriction

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalRings GeometricScalarRestriction SolidAnalyticModules
open AdicSolidGenerators

variable {A B : Type 1} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [CommRing B] [TopologicalSpace B]
  [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ)

/-- The actual continuous map on every continuous-function ring. -/
def sectionMap (S : CompHaus.{0}ᵒᵖ) : C(S.unop, A) →+* C(S.unop, B) where
  toFun a := ⟨fun s ↦ φ (a s), hφ.comp a.continuous⟩
  map_zero' := by ext s; exact map_zero φ
  map_one' := by ext s; exact map_one φ
  map_add' a b := by ext s; exact map_add φ (a s) (b s)
  map_mul' a b := by ext s; exact map_mul φ (a s) (b s)

/-- The actual change of condensed structural ring sheaves. -/
def ringMap : ringSheaf A ⟶
    ((𝟭 CompHaus.{0}).sheafPushforwardContinuous RingCat.{1}
      (coherentTopology CompHaus.{0}) (coherentTopology CompHaus.{0})).obj
        (ringSheaf B) where
  hom :=
    { app S := RingCat.ofHom (sectionMap φ hφ S)
      naturality S T f := by ext a; rfl }

/-- Actual restriction of scalars between geometric topological modules. -/
def restriction : GeometricModules B ⥤ GeometricModules A :=
  SheafOfModules.pushforward.{1} (F := 𝟭 CompHaus.{0}) (ringMap φ hφ)

instance restriction_additive : (restriction φ hφ).Additive where
  map_add := rfl

section Extension

variable [(restriction φ hφ).IsRightAdjoint]

/-- Native scalar extension along the actual continuous ring map. -/
def extension : GeometricModules A ⥤ GeometricModules B :=
  (restriction φ hφ).leftAdjoint

/-- Its native extension/restriction adjunction. -/
def adjunction : extension φ hφ ⊣ restriction φ hφ :=
  Adjunction.ofIsRightAdjoint (restriction φ hφ)

/-- The actual coefficient unit map. -/
def unitRestriction : SheafOfModules.unit (ringSheaf A) ⟶
    (restriction φ hφ).obj (SheafOfModules.unit (ringSheaf B)) :=
  SheafOfModules.unitToPushforwardObjUnit (ringMap φ hφ)

/-- Its adjunction mate is the actual scalar-extension unit comparison. -/
def unitExtension : (extension φ hφ).obj (SheafOfModules.unit (ringSheaf A)) ⟶
    SheafOfModules.unit (ringSheaf B) :=
  (adjunction φ hφ).homEquiv _ _ |>.symm (unitRestriction φ hφ)

/-- The two coefficient unit maps have their native mate normalization. -/
theorem unitExtension_mate :
    (adjunction φ hφ).homEquiv _ _ (unitExtension φ hφ) = unitRestriction φ hφ :=
  (adjunction φ hφ).homEquiv _ _ |>.apply_symm_apply _

end Extension

section DerivedExtension

variable [(restriction φ hφ).IsRightAdjoint]

instance extension_additive : (extension φ hφ).Additive :=
  (adjunction φ hφ).left_adjoint_additive

attribute [local instance] HasDerivedCategory.standard

/-- The actual cochain scalar extension, followed by the native derived quotient. -/
def derivedExtensionSource : CochainComplex (GeometricModules A) ℤ ⥤
    DerivedCategory (GeometricModules B) :=
  (extension φ hφ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

instance derivedExtensionSource_shift : (derivedExtensionSource φ hφ).CommShift ℤ :=
  inferInstanceAs (((extension φ hφ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).CommShift ℤ)

/-- Derived existence is requested for this fixed ordinary scalar-extension source. -/
class HasDerivedExtension : Prop where
  exists_derived : (derivedExtensionSource φ hφ).HasLeftDerivedFunctor
    (HomologicalComplex.quasiIso (GeometricModules A) (ComplexShape.up ℤ))

attribute [instance] HasDerivedExtension.exists_derived

/-- Native Kan-derived scalar extension of the actual geometric rings. -/
def derivedExtension [HasDerivedExtension φ hφ] :
    DerivedCategory (GeometricModules A) ⥤ DerivedCategory (GeometricModules B) :=
  (derivedExtensionSource φ hφ).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (GeometricModules A) (ComplexShape.up ℤ))

/-- The native comparison on the original cochain source. -/
def derivedExtensionCounit [HasDerivedExtension φ hφ] :
    DerivedCategory.Q ⋙ derivedExtension φ hφ ⟶ derivedExtensionSource φ hφ :=
  (derivedExtensionSource φ hφ).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (GeometricModules A) (ComplexShape.up ℤ))

end DerivedExtension

attribute [local instance] HasDerivedCategory.standard

/-- Native derived extension together with its source-forced shift structure. -/
structure ShiftedExtensionModel where
  [adjoint : (restriction φ hφ).IsRightAdjoint]
  [derived : HasDerivedExtension φ hφ]
  [shift : (derivedExtension φ hφ).CommShift ℤ]
  [counitShift : NatTrans.CommShift (derivedExtensionCounit φ hφ) ℤ]

/-- The functor of this model is the actual native Kan-derived extension. -/
def ShiftedExtensionModel.functor (E : ShiftedExtensionModel φ hφ) :
    DerivedCategory (GeometricModules A) ⥤ DerivedCategory (GeometricModules B) :=
  letI := E.adjoint
  letI := E.derived
  derivedExtension φ hφ

instance shiftedExtension_shift (E : ShiftedExtensionModel φ hφ) :
    (E.functor φ hφ).CommShift ℤ := by
  letI := E.adjoint
  letI := E.derived
  exact E.shift

attribute [local instance] HasDerivedCategory.standard

/-- The fixed ordinary cochain restriction followed by the native quotient. -/
def derivedRestrictionSource : CochainComplex (GeometricModules B) ℤ ⥤
    GeometricDerived A :=
  (restriction φ hφ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- Existence of the derived functor of this specific ordinary source. -/
class HasDerivedRestriction : Prop where
  exists_derived : (derivedRestrictionSource φ hφ).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (GeometricModules B) (ComplexShape.up ℤ))

attribute [instance] HasDerivedRestriction.exists_derived

/-- The native Kan-derived restriction of these actual coefficients. -/
def derivedRestriction [HasDerivedRestriction φ hφ] :
    GeometricDerived B ⥤ GeometricDerived A :=
  (derivedRestrictionSource φ hφ).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (GeometricModules B) (ComplexShape.up ℤ))

variable [HasDerivedRestriction φ hφ]

/-- Analytic preservation is tested on the actual integer/polynomial restrictions. -/
def PreservesAnalytic (S : Subring A) (T : Subring B)
    (E : RestrictionInput A S) (F : RestrictionInput B T) : Prop :=
  ∀ K : GeometricDerived B, IsAnalyticComplete B T F K →
    IsAnalyticComplete A S E ((derivedRestriction φ hφ).obj K)

/-- The comparison is uniquely induced by the prescribed analytic units. -/
def analyticComparison {S : Subring A} {T : Subring B}
    {E : RestrictionInput A S} {F : RestrictionInput B T}
    (L : AnalyticReflection A S E) (M : AnalyticReflection B T F)
    (h : PreservesAnalytic φ hφ S T E F) (K : GeometricDerived B) :
    L.functor.obj ((derivedRestriction φ hφ).obj K) ⟶
      (derivedRestriction φ hφ).obj (M.functor.obj K) :=
  (Equiv.ofBijective _ (L.universal _ _ (h _ (M.complete K)))).symm
    ((derivedRestriction φ hφ).map (M.unit.app K))

/-- The analytic comparison commutes with the actual source units. -/
theorem analyticComparison_unit {S : Subring A} {T : Subring B}
    {E : RestrictionInput A S} {F : RestrictionInput B T}
    (L : AnalyticReflection A S E) (M : AnalyticReflection B T F)
    (h : PreservesAnalytic φ hφ S T E F) (K : GeometricDerived B) :
    L.unit.app ((derivedRestriction φ hφ).obj K) ≫ analyticComparison φ hφ L M h K =
      (derivedRestriction φ hφ).map (M.unit.app K) :=
  (Equiv.ofBijective _ (L.universal _ _ (h _ (M.complete K)))).apply_symm_apply _

/-- Internal adic preservation tests all actual localized profinite generators. -/
def PreservesComplete (I : Ideal A) (J : Ideal B) : Prop :=
  ∀ K : GeometricDerived B, IsComplete B J K →
    IsComplete A I ((derivedRestriction φ hφ).obj K)

/-- The fixed adic completion-unit comparison for the actual restrictions. -/
def completionComparison {I : Ideal A} {J : Ideal B}
    (L : CompletionModel A I) (M : CompletionModel B J)
    (h : PreservesComplete φ hφ I J) (K : GeometricDerived B) :
    L.functor.obj ((derivedRestriction φ hφ).obj K) ⟶
      (derivedRestriction φ hφ).obj (M.functor.obj K) :=
  (Equiv.ofBijective _ (L.universal _ _ (h _ (M.complete K)))).symm
    ((derivedRestriction φ hφ).map (M.unit.app K))

end MathlibExt.Condensed.GeometricTopologicalRestriction
