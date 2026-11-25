/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativePrismaticNygaardSource
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Relative Nygaard and décalage comparison requests

References: Bhatt–Scholze, arXiv:1905.08229v4, Theorems 15.2–15.3;
BMS19 arXiv:1802.03261v2, Proposition 5.8.
The existing `RelativeNygaardInitialPrismWanted.initialPrismLift` supplies
the initial lifts on the actual large basis. These companions assemble
the base-module/Frobenius dictionary and bind the qsyn comparison to the
actual affine coordinates, sheafification units and native derived-section
units. No perfect-base or properness assumption is added. Graded comparison
and décalage invertibility are outputs, never background fields.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeQuasiSyntomicNygaard

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.PadicFormalSchemes
open MathlibExt.AlgebraicGeometry.RelativePrismaticNygaardSource

attribute [local instance] HasDerivedCategory.standard

public def_wanted relativeNygaardFrobeniusDiagram
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal)) :
    Σ' h : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      IsComplete P.ring (completionIdeal p P.ideal)
        (PrismaticNygaardModels.deltaObject p P B.obj.ring (D B).lift),
      RelativeQuasiSyntomicNygaard.FrobeniusDiagram p P R D C h

public def_wanted relativeQsynBasisBinding
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring) :
    BasisSiteBinding p P R X A D

public theorem_wanted relativeBasisContinuous
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D) :
    B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)

public def_wanted relativeStructuralComparison
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D)
    [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)] : B.StructuralComparison

public def_wanted relativeDerivedRestriction
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D)
    [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)] :
    B.HasDerivedRestriction

public theorem_wanted relativeDerivedStructuralComparison
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D)
    [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)]
    [B.HasDerivedRestriction] (S : B.StructuralComparison) : IsIso (B.derivedStructuralMap S)

public def_wanted relativeGlobalSectionMap
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D)
    [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)]
    [B.HasDerivedRestriction]
    [RelativePrismaticCohomology.HasDerivedSections p P X]
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R] : B.GlobalSectionMap

public theorem_wanted relativePrismaticDescent
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (B : BasisSiteBinding p P R X A D)
    [B.functor.IsContinuous (RelativeQuasiSyntomicNygaard.topology p P R)
      (RelativePrismaticSite.topology p P X)]
    [B.HasDerivedRestriction]
    [RelativePrismaticCohomology.HasDerivedSections p P X]
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
    (S : B.StructuralComparison) (G : B.GlobalSectionMap) [IsIso (B.derivedStructuralMap S)]
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) : IsIso (B.globalComparison S G)

public theorem_wanted relativeCompletedTwist
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    Nonempty ((completedExtension (DeltaRing.frobenius p P.ring) C).obj
      (RelativeQuasiSyntomicNygaard.delta p P R D) ≅ RelativeQuasiSyntomicNygaard.twisted p P R D C)

public theorem_wanted relativeNygaardGraded
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      IsComplete P.ring (completionIdeal p P.ideal)
        (PrismaticNygaardModels.deltaObject p P B.obj.ring (D B).lift))
    (F : RelativeQuasiSyntomicNygaard.FrobeniusDiagram p P R D C h)
    [HasExtension (Ideal.Quotient.mk P.ideal)] [HasTensor P.Residue]
    (V : Completion P.Residue (Ideal.span {(p : P.Residue)})) (i : ℕ)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    Nonempty (RelativeQuasiSyntomicNygaard.graded p P R D F i ≅ hodgeGradedTarget p P R D V i)

public def_wanted connectiveRelativePrismaticModel
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    Σ K : CochainComplex (Modules P.ring) ℕ,
      {e : DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) ≅
        RelativeQuasiSyntomicNygaard.delta p P R D // PrismaticDecalageModels.IsIdealRegularModel P.ideal K}

public def_wanted relativeFrobeniusDecalage
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (R : CommAlgCat.{0} P.Residue)
    (X : FormalScheme p P.ring P.ideal) (A : AffinePresentation p P R X)
    [RelativeQuasiSyntomicNygaard.HasDerivedSections p P R]
    (D : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      PrismaticNygaardModels.InitialLift p P B.obj.ring)
    [HasExtension (DeltaRing.frobenius p P.ring)]
    (C : Completion P.ring (completionIdeal p P.ideal))
    (h : ∀ B : RelativeQuasiSyntomicNygaard.Basis p P R,
      IsComplete P.ring (completionIdeal p P.ideal)
        (PrismaticNygaardModels.deltaObject p P B.obj.ring (D B).lift))
    (F : RelativeQuasiSyntomicNygaard.FrobeniusDiagram p P R D C h)
    (K : CochainComplex (Modules P.ring) ℕ)
    (e : DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) ≅
      RelativeQuasiSyntomicNygaard.delta p P R D)
    (hRegular : PrismaticDecalageModels.IsIdealRegularModel P.ideal K)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    {f : RelativeQuasiSyntomicNygaard.twisted p P R D C ⟶
      PrismaticDecalageModels.derived P.ideal K //
      f ≫ DerivedCategory.Q.map (PrismaticDecalageModels.inclusion P.ideal K) ≫ e.hom =
        RelativeQuasiSyntomicNygaard.frobeniusGlobal p P R D F ∧ IsIso f}

end WantedExt.AlgebraicGeometry.RelativeQuasiSyntomicNygaard
