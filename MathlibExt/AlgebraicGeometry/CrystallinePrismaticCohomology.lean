/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), `AlgebraicGeometry.hasSheafify_moduleCat`:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: expose the equal-universe small-site specialization needed by Mathlib's
Grothendieck-category equivalence.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import
  Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import MathlibExt.AlgebraicGeometry.CrystallinePrismaticSite
public import MathlibExt.AlgebraicGeometry.PrimeFieldDeRham
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Actual crystalline-prismatic derived sections and specialization

Prismatic cohomology is computed by applying the actual global-section
limit functor to an injective resolution of the structural sheaf of the
actual δ-lift site. Frobenius is the lift of its fixed sheaf endomorphism
through that resolution, with the usual resolution-unit normalization.

Over the actual prism `(Z_p,(p))`, whose Frobenius is the identity,
derived scalar extension to `F_p` is represented by the mapping cone of
multiplication by p. The comparison target is the actual right-derived
global sections of the normalized prime-field de Rham complex.

References: Bhatt–Scholze, *Prisms and prismatic cohomology*, Definition
4.1 and Theorem 1.8(3), https://arxiv.org/abs/1905.08229.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.CrystallinePrismaticCohomology

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open CrystallinePrismaticSite CoherentCurveLinearSeries

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]
  (X : CrystallinePrismaticSite.PrimeFieldScheme p)

abbrev Coefficients := ModuleCat.{1} (PadicInt p)
abbrev Sheaves := Sheaf (topology p X) (Coefficients p)

instance coefficientsLimits : HasLimitsOfSize.{1, 1} (Coefficients p) :=
  ModuleCat.hasLimitsOfSize.{1, 1, 1, 0}

instance coefficientsSiteLimits :
    HasLimitsOfShape (Obj p X)ᵒᵖ (Coefficients p) := by
  let : HasLimitsOfSize.{0, 1} (Coefficients p) :=
    ModuleCat.hasLimitsOfSize.{0, 1, 1, 0}
  infer_instance

instance coefficientsGrothendieck :
    IsGrothendieckAbelian.{1} (Coefficients p) :=
  IsGrothendieckAbelian.of_equivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{1} (PadicInt p) ≃+* PadicInt p).symm)

instance moduleSheafifySmall {C : Type 1} [SmallCategory C]
    (J : GrothendieckTopology C) : HasSheafify J (Coefficients p) := by
  let : PreservesColimitsOfSize.{1, 1}
      (forget₂ (Coefficients p) AddCommGrpCat.{1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{1, 0, 1, 1} (PadicInt p)
  let : PreservesFilteredColimits (forget (Coefficients p)) :=
    comp_preservesFilteredColimits.{1, 1}
      (forget₂ (Coefficients p) AddCommGrpCat.{1})
      (forget AddCommGrpCat.{1})
  let : PreservesFilteredColimitsOfSize.{1, 1}
      (forget (Coefficients p)) := inferInstance
  infer_instance

instance sheavesGrothendieck : IsGrothendieckAbelian.{1} (Sheaves p X) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{1, 1, 0, 2, 1}
    (topology p X) (Coefficients p)

/-- Ordinary global sections are the actual limit of the structural diagram. -/
def globalSections : Sheaves p X ⥤ Coefficients p :=
  sheafToPresheaf (topology p X) (Coefficients p) ⋙ lim.{0, 1, 1, 2}

instance globalSections_additive : (globalSections p X).Additive where
  map_add {F G f g} := by
    change limMap (f.hom + g.hom) = limMap f.hom + limMap g.hom
    apply limit.hom_ext
    intro U
    simp [Preadditive.add_comp, Preadditive.comp_add]

/-- The actual chosen injective resolution of the structural sheaf. -/
abbrev resolution : InjectiveResolution (structureSheaf p X) :=
  injectiveResolution (structureSheaf p X)

/-- These cochains compute RΓ of the actual prismatic structural sheaf. -/
def complex : CochainComplex (Coefficients p) ℤ :=
  (((globalSections p X).mapHomologicalComplex _).obj
    (resolution p X).cocomplex).extend ComplexShape.embeddingUpNat

def derived : DerivedCategory (Coefficients p) :=
  DerivedCategory.Q.obj (complex p X)

/-- Lift the actual sheaf Frobenius by the native resolution constructor. -/
def frobeniusResolution :
    (resolution p X).cocomplex ⟶ (resolution p X).cocomplex :=
  InjectiveResolution.desc (frobeniusSheaf p X)
    (resolution p X) (resolution p X)

/-- Its defining normalization is the actual resolution-unit square. -/
theorem frobeniusResolution_unit :
    (resolution p X).ι ≫ frobeniusResolution p X =
      (CochainComplex.single₀ (Sheaves p X)).map (frobeniusSheaf p X) ≫
        (resolution p X).ι :=
  InjectiveResolution.desc_commutes _ _ _

def frobeniusComplex : complex p X ⟶ complex p X :=
  (ComplexShape.embeddingUpNat.extendFunctor (Coefficients p)).map
    (((globalSections p X).mapHomologicalComplex _).map
      (frobeniusResolution p X))

def frobenius : derived p X ⟶ derived p X :=
  DerivedCategory.Q.map (frobeniusComplex p X)

/-- The two-term free resolution of F_p gives this actual derived mod-p cone.
The scalar map is along the actual identity prism Frobenius. -/
def specialization : DerivedCategory (Coefficients p) :=
  DerivedCategory.Q.obj
    (CochainComplex.mappingCone ((p : PadicInt p) • 𝟙 (complex p X)))

/-- The only universe change is the actual linear ULift constructor. -/
def liftModules (R : Type) [Ring R] : ModuleCat.{0} R ⥤ ModuleCat.{1} R where
  obj M := ModuleCat.of R (ULift.{1} M)
  map f := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{1} _ ≃ₗ[R] _).symm.toLinearMap.comp
      (f.hom.comp (ULift.moduleEquiv : ULift.{1} _ ≃ₗ[R] _).toLinearMap))
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

instance liftModules_additive (R : Type) [Ring R] :
    (liftModules R).Additive where
  map_add := rfl

def fpSections : X.left.Modules ⥤ ModuleCat.{1} (ZMod p) :=
  sectionsFunctor X.hom ⋙ liftModules (ZMod p)

instance fpSections_additive : (fpSections p X).Additive := by
  dsimp only [fpSections]
  infer_instance

/-- The actual bounded-below de Rham complex. -/
def deRhamPlus (D : PrimeFieldDeRham.Differential p X) :
    CochainComplex.Plus X.left.Modules where
  obj := D.complex
  property := by
    refine ⟨0, ?_⟩
    dsimp only [PrimeFieldDeRham.Differential.complex]
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply HomologicalComplex.isZero_extend_X
    intro n hn
    change (n : ℤ) = i at hn
    have hn₀ := Int.natCast_nonneg n
    rw [hn] at hn₀
    exact (not_le_of_gt hi) hn₀

/-- Right-derived prime-field sections of the genuine de Rham complex. -/
def deRhamFp (D : PrimeFieldDeRham.Differential p X) :
    DerivedCategory (ModuleCat.{1} (ZMod p)) :=
  ((fpSections p X).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι).obj
      (DerivedCategory.Plus.Q.obj (deRhamPlus p X D))

/-- Read the actual de Rham object over Z_p via its fixed residue map. -/
def deRham (D : PrimeFieldDeRham.Differential p X) :
    DerivedCategory (Coefficients p) :=
  DerivedCategory.Q.obj
    (((ModuleCat.restrictScalars
      (PadicInt.toZMod : PadicInt p →+* ZMod p)).mapHomologicalComplex _).obj
        (DerivedCategory.Q.objPreimage (deRhamFp p X D)))

end MathlibExt.AlgebraicGeometry.CrystallinePrismaticCohomology
