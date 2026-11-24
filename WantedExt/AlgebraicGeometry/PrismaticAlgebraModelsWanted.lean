/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange

/-!
# Normalized prismatic algebra and Cartesian base-change requests

The actual structural rings, alternating coface differential, tensor
generators, cups, units, coefficient maps, scalar linearizations and
completion units are fixed in MathlibExt. These direct requests assemble
generic algebra/sheaf hypermodels and the source geometric isomorphism.

Compatible source and target hypermodels are constructed together;
an arbitrary pair of nonfunctorial resolutions is not assumed to admit
a strict algebra map. The comparison preserves the fixed cup and unit
because its cochain realization is an AlgebraMap, not merely a module iso.

References: Bhatt--Scholze, arXiv:1905.08229v4, Theorem 1.8(5),
Corollary 4.12; Stacks Project, Tags 015G, 01FM and 0FKM. The global base change is requested
for quasi-compact and quasi-separated formal schemes only.
The E-infinity enhancement and the normalized global de Rham comparison
are distinct from this ordinary derived-algebra component.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PrismaticAlgebraModels

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
open MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels
open MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange
open MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology
open MathlibExt.AlgebraicGeometry.PadicFormalSchemes
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Assemble the structural algebra sheaf, normalized by actual module sheafification. -/
public def_wanted structuralAlgebra
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) : StructuralAlgebra p P X

/-- Assemble a genuine generic acyclic algebra hyperresolution of this fixed sheaf. -/
public def_wanted algebraHypermodel
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) [HasDerivedSections p P X]
    (O : StructuralAlgebra p P X) : Hypermodel p P X O

/-- Assemble the actual cosimplicial cup, scalar unit and Koszul commutativity homotopy. -/
public def_wanted cosimplicialAlgebra
    (A : Type) [CommRing A] (F : AlgebraDiagram A) : AlgebraAssembly F

/-- Realize the actual coefficient ring maps as a cup/unit-preserving cochain map. -/
public def_wanted coefficientAlgebraMap
    (A B : Type) [CommRing A] [CommRing B] (f : A →+* B)
    (F : AlgebraDiagram A) (G : AlgebraDiagram B)
    (c : CoefficientRingMap f F G) (M : AlgebraAssembly F) (N : AlgebraAssembly G) :
    AlgebraMap f F G c M N

/-- Construct compatible hypermodels and their actual site-section maps together. -/
public def_wanted baseChangeHypermodels
    (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) (Y : FormalScheme p Q.ring Q.ideal)
    [HasDerivedSections p P X] [HasDerivedSections p Q Y]
    (g : MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps.Map p P Q X Y)
    (O : StructuralAlgebra p P X) (V : StructuralAlgebra p Q Y) :
    Σ H : Hypermodel p P X O, Σ K : Hypermodel p Q Y V,
      SiteAlgebraMap p P Q X Y g H K

/-- The actual relative prismatic derived object is derived complete in the smooth scope. -/
public theorem_wanted prismaticIsComplete
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) [HasDerivedSections p P X]
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    IsComplete P.ring (completionIdeal p P.ideal) (prismatic p P X)

/-- The source's base-change isomorphism on the actual normalized completed algebra map, for
quasi-compact and quasi-separated `X`. Bhatt–Scholze, Cor. 4.12, is local, on the étale site; on
global sections it is obtained from finite affine hypercovers, which need the qcqs hypothesis:
for a countable disjoint union of copies of the base, the completed tensor product does not
commute with the infinite product of global sections. -/
public theorem_wanted cartesianBaseChange
    (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) (Y : FormalScheme p Q.ring Q.ideal)
    [HasDerivedSections p P X] [HasDerivedSections p Q Y]
    (g : MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps.Map p P Q X Y)
    [HasExtension g.base.hom]
    (O : StructuralAlgebra p P X) (V : StructuralAlgebra p Q Y)
    (H : Hypermodel p P X O) (K : Hypermodel p Q Y V)
    (s : SiteAlgebraMap p P Q X Y g H K)
    (M : AlgebraAssembly H.globalDiagram) (N : AlgebraAssembly K.globalDiagram)
    (a : AlgebraMap g.base.hom H.globalDiagram K.globalDiagram s.coefficient M N)
    (C : Completion Q.ring (completionIdeal p Q.ideal))
    (hComplete : IsComplete Q.ring (completionIdeal p Q.ideal)
      (DerivedCategory.Q.obj (complex K.globalDiagram)))
    (hCartesian : IsCartesian p P Q X Y g)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (hQcqs : ∀ n : ℕ, QuasiCompact (X.structureMap.app n) ∧
      QuasiSeparated (X.structureMap.app n)) :
    IsIso (s.prismaticMap a C hComplete)

end WantedExt.AlgebraicGeometry.PrismaticAlgebraModels
