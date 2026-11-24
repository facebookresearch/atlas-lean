/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeQuasiSyntomicNygaard
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Source binding for relative quasisyntomic/prismatic comparisons

The original formal affine presentation is fixed on every nilpotent level.
The basis-site binding uses the actual initial prisms, their universal maps
and all original affine coordinates, including nilpotents. Structural sheaf
comparison uses the actual sheafification unit. The global comparison uses
the native section-limit restriction and the right-derived section units on
every cochain complex. No freely named canonical comparison map is supplied.

Hodge–Tate reduction uses A → A/I without phi_A. Its twist is the actual
conormal tensor power I/I², followed by derived tensor and native truncation.
The phi_A-completed de Rham scalar map is the distinct existing operation.

Reference: Bhatt–Scholze, arXiv:1905.08229v4, Theorems 15.2–15.3.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePrismaticNygaardSource

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
  _root_.AlgebraicGeometry
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open PadicFormalSchemes
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (R : CommAlgCat.{0} P.Residue) (X : FormalScheme p P.ring P.ideal)

def affineScalars : P.ring →+* R :=
  (algebraMap P.Residue R).comp (Ideal.Quotient.mk P.ideal)

theorem affineScalars_ideal : P.ideal.map (affineScalars p P R) ≤ (⊥ : Ideal R) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change affineScalars p P R a ∈ (⊥ : Ideal R)
  rw [Ideal.mem_bot]
  change algebraMap P.Residue R (Ideal.Quotient.mk P.ideal a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def affineBase : spfDiagram p R ⊥ ⟶ spfDiagram p P.ring P.ideal :=
  mapDiagram p (affineScalars p P R) (affineScalars_ideal p P R)

/-- An actual p-complete affine formal presentation. Completeness of the
displayed ring is explicit: the nilpotent diagram alone remembers only its
completion. This is geometry input, independent of the comparison theorem. -/
structure AffinePresentation where
  complete : IsCompleteRing R (Ideal.span {(p : R)})
  iso : spfDiagram p R ⊥ ≅ X.diagram
  base : iso.hom ≫ X.structureMap = affineBase p P R

variable (A : AffinePresentation p P R X)
  (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
    PrismaticNygaardModels.InitialLift p P B.obj.ring)

/-- Every formal point is fixed on all coefficients of all nilpotent levels.
The universal initial-prism maps also fix every source-site arrow. -/
structure BasisSiteBinding where
  point : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
    spfDiagram p (D B).lift.prism.ring (D B).lift.prism.ideal ⟶ X.diagram
  base : ∀ B, point B ≫ X.structureMap =
    mapDiagram p (D B).lift.base.hom (D B).lift.base.ideal
  coordinates : ∀ (B : RelativeQuasiSyntomicNygaard.Basis p P R) (n : ℕ) (r : R),
    ((Scheme.ΓSpecIso (CommRingCat.of (LevelRing p R ⊥ n))).inv ≫
      ((point B).app n ≫ A.iso.inv.app n).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of
        (LevelRing p (D B).lift.prism.ring (D B).lift.prism.ideal n))).hom)
      (Ideal.Quotient.mk (levelIdeal p R ⊥ n) r) =
        residueToLevel p (D B).lift.prism.ring (D B).lift.prism.ideal n
          ((D B).lift.residue (B.obj.under r))
  arrows : ∀ {U V : RelativeQuasiSyntomicNygaard.Basis p P R} (f : U ⟶ V),
    mapDiagram p (RelativeQuasiSyntomicNygaard.map p P R D f).hom
      (RelativeQuasiSyntomicNygaard.map p P R D f).ideal ≫ point U = point V

namespace BasisSiteBinding

variable {p P R X A D} (B : BasisSiteBinding p P R X A D)

def functor : (RelativeQuasiSyntomicNygaard.Basis p P R)ᵒᵖ ⥤ RelativePrismaticSite.Obj p P X where
  obj U := ⟨(D U.unop).lift.prism, (D U.unop).lift.base, B.point U.unop, B.base U.unop⟩
  map f :=
    ⟨RelativeQuasiSyntomicNygaard.map p P R D f.unop,
      RelativeQuasiSyntomicNygaard.initialMap_base p P (D _) (D _) f.unop.hom.map,
      B.arrows f.unop⟩
  map_id U := by
    apply RelativePrismaticSite.Hom.ext
    exact RelativeQuasiSyntomicNygaard.initialMap_id p P (D U.unop)
  map_comp f g := by
    apply RelativePrismaticSite.Hom.ext
    exact RelativeQuasiSyntomicNygaard.initialMap_comp p P (D _) (D _) (D _)
      g.unop.hom.map f.unop.hom.map

def structuralPresheafIso : RelativeQuasiSyntomicNygaard.deltaPresheaf p P R D ≅
    B.functor.op ⋙ RelativePrismaticSite.structurePresheaf p P X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro U V f; ext x; rfl)

variable [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
    (RelativePrismaticSite.topology p P X)]

def restriction : RelativePrismaticCohomology.Sheaves p P X ⥤
    RelativeQuasiSyntomicNygaard.Sheaves p P R :=
  B.functor.sheafPushforwardContinuous (Modules P.ring)
    (RelativeQuasiSyntomicNygaard.topology p P R) (RelativePrismaticSite.topology p P X)

instance restriction_additive : B.restriction.Additive where
  map_add := by intros; rfl

def structuralUnit : RelativeQuasiSyntomicNygaard.deltaPresheaf p P R D ⟶
    (B.restriction.obj (RelativePrismaticSite.structureSheaf p P X)).obj :=
  B.structuralPresheafIso.hom ≫ whiskerLeft B.functor.op
    (toSheafify (RelativePrismaticSite.topology p P X)
      (RelativePrismaticSite.structurePresheaf p P X))

structure StructuralComparison where
  iso : RelativeQuasiSyntomicNygaard.deltaSheaf p P R D ≅
    B.restriction.obj (RelativePrismaticSite.structureSheaf p P X)
  unit : toSheafify (RelativeQuasiSyntomicNygaard.topology p P R)
    (RelativeQuasiSyntomicNygaard.deltaPresheaf p P R D) ≫ iso.hom.hom = B.structuralUnit

/-- Restriction is the actual native limit map, with every projection fixed. -/
def sectionRestriction : RelativePrismaticCohomology.sections p P X ⟶
    B.restriction ⋙ RelativeQuasiSyntomicNygaard.sections p P R where
  app M := limit.pre M.obj B.functor.op
  naturality {M N} f := by
    apply limit.hom_ext
    intro U
    change (limMap f.hom ≫ limit.pre N.obj B.functor.op) ≫
        limit.π (B.functor.op ⋙ N.obj) U =
      (limit.pre M.obj B.functor.op ≫ limMap (whiskerLeft B.functor.op f.hom)) ≫
        limit.π (B.functor.op ⋙ N.obj) U
    simp

def sectionsCochainMap (K : CochainComplex (RelativePrismaticCohomology.Sheaves p P X) ℤ) :
    ((RelativePrismaticCohomology.sections p P X).mapHomologicalComplex (.up ℤ)).obj K ⟶
    ((RelativeQuasiSyntomicNygaard.sections p P R).mapHomologicalComplex (.up ℤ)).obj
      ((B.restriction.mapHomologicalComplex (.up ℤ)).obj K) where
  f i := B.sectionRestriction.app (K.X i)
  comm' i j _ := (B.sectionRestriction.naturality (K.d i j)).symm

def restrictionSource : CochainComplex (RelativePrismaticCohomology.Sheaves p P X) ℤ ⥤
    DerivedCategory (RelativeQuasiSyntomicNygaard.Sheaves p P R) :=
  B.restriction.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

class HasDerivedRestriction : Prop where
  exists_derived : B.restrictionSource.HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (RelativePrismaticCohomology.Sheaves p P X) (.up ℤ))

attribute [instance] HasDerivedRestriction.exists_derived

variable [B.HasDerivedRestriction]

def derivedRestriction : DerivedCategory (RelativePrismaticCohomology.Sheaves p P X) ⥤
    DerivedCategory (RelativeQuasiSyntomicNygaard.Sheaves p P R) :=
  B.restrictionSource.totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (RelativePrismaticCohomology.Sheaves p P X) (.up ℤ))

def derivedRestrictionUnit : B.restrictionSource ⟶ DerivedCategory.Q ⋙ B.derivedRestriction :=
  B.restrictionSource.totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (RelativePrismaticCohomology.Sheaves p P X) (.up ℤ))

def structuralCochainMap (S : B.StructuralComparison) :
    (HomologicalComplex.single (RelativeQuasiSyntomicNygaard.Sheaves p P R) (.up ℤ) 0).obj
      (RelativeQuasiSyntomicNygaard.deltaSheaf p P R D) ⟶
    (B.restriction.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single (RelativePrismaticCohomology.Sheaves p P X) (.up ℤ) 0).obj
        (RelativePrismaticSite.structureSheaf p P X)) :=
  HomologicalComplex.mkHomFromSingle
    (S.iso.hom ≫ B.restriction.map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (RelativePrismaticSite.structureSheaf p P X)).inv)
    (fun j hj ↦ by simp)

/-- The derived structural map uses the prescribed ordinary structural
comparison and the native right-derived restriction unit. -/
def derivedStructuralMap (S : B.StructuralComparison) :
    (DerivedCategory.singleFunctor (RelativeQuasiSyntomicNygaard.Sheaves p P R) 0).obj
      (RelativeQuasiSyntomicNygaard.deltaSheaf p P R D) ⟶
    B.derivedRestriction.obj
      ((DerivedCategory.singleFunctor (RelativePrismaticCohomology.Sheaves p P X) 0).obj
        (RelativePrismaticSite.structureSheaf p P X)) :=
  DerivedCategory.Q.map (B.structuralCochainMap S) ≫ B.derivedRestrictionUnit.app
    ((HomologicalComplex.single (RelativePrismaticCohomology.Sheaves p P X) (.up ℤ) 0).obj
      (RelativePrismaticSite.structureSheaf p P X))

variable [RelativePrismaticCohomology.HasDerivedSections p P X]
  [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]

/-- A source-normalized native right-derived lift, constrained on every
cochain complex by both specified derived-section units. -/
structure GlobalSectionMap where
  map : RelativePrismaticCohomology.derivedSections p P X ⟶
    B.derivedRestriction ⋙ RelativeQuasiSyntomicNygaard.derivedSections p P R
  unit : ∀ K : CochainComplex (RelativePrismaticCohomology.Sheaves p P X) ℤ,
    (RelativePrismaticCohomology.derivedSectionsUnit p P X).app K ≫
      map.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (B.sectionsCochainMap K) ≫
          ((RelativeQuasiSyntomicNygaard.sectionsSource p P R).totalRightDerivedUnit
            DerivedCategory.Q
            (HomologicalComplex.quasiIso (RelativeQuasiSyntomicNygaard.Sheaves p P R)
              (.up ℤ))).app ((B.restriction.mapHomologicalComplex (.up ℤ)).obj K) ≫
          (RelativeQuasiSyntomicNygaard.derivedSections p P R).map
            (B.derivedRestrictionUnit.app K)

def globalComparison (S : B.StructuralComparison) (G : B.GlobalSectionMap)
    [IsIso (B.derivedStructuralMap S)] :
    RelativePrismaticCohomology.prismatic p P X ⟶ RelativeQuasiSyntomicNygaard.delta p P R D :=
  G.map.app ((DerivedCategory.singleFunctor (RelativePrismaticCohomology.Sheaves p P X) 0).obj
    (RelativePrismaticSite.structureSheaf p P X)) ≫
      (RelativeQuasiSyntomicNygaard.derivedSections p P R).map
        (inv (B.derivedStructuralMap S))

end BasisSiteBinding

/-- Native good truncation of the specified derived object. -/
def truncLE (K : DerivedCategory (Modules P.Residue)) (i : ℤ) :
    DerivedCategory (Modules P.Residue) :=
  DerivedCategory.Q.obj ((DerivedCategory.Q.objPreimage K).truncLE i)

def conormal : Modules P.Residue :=
  ModuleCat.of P.Residue (ULift.{1} P.ideal.Cotangent)

def conormalPower : ℕ → Modules P.Residue
  | 0 => ModuleCat.of P.Residue (ULift.{1} P.Residue)
  | i + 1 => ModuleCat.of P.Residue (conormal p P ⊗[P.Residue] conormalPower i)

variable [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
  [HasExtension (Ideal.Quotient.mk P.ideal)] [HasTensor P.Residue]
  (C : Completion P.Residue (Ideal.span {(p : P.Residue)}))

def hodgeTate : DerivedCategory (Modules P.Residue) :=
  (completedExtension (Ideal.Quotient.mk P.ideal) C).obj
    (RelativeQuasiSyntomicNygaard.delta p P R D)

def hodgeTateTwist (i : ℕ) : DerivedCategory (Modules P.Residue) :=
  completedTensor C (hodgeTate p P R D C)
    ((DerivedCategory.singleFunctor (Modules P.Residue) 0).obj (conormalPower p P i))

def hodgeGradedTarget (i : ℕ) : DerivedCategory (Modules P.ring) :=
  (ModuleCat.restrictScalars.{1, 0, 0} (Ideal.Quotient.mk P.ideal)).mapDerivedCategory.obj
    (truncLE p P (hodgeTateTwist p P R D C i) (i : ℤ))

end MathlibExt.AlgebraicGeometry.RelativePrismaticNygaardSource
