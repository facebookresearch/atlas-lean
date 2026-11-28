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

/-- The prismatic structure sheaf as a sheaf of algebras: let $p$ be a prime, $(A, I)$ a bounded
prism and $X$ a $p$-adic formal scheme over $\operatorname{Spf}(A/I)$ (`FormalScheme`, with levels
over $A/(I+(p)^{n+1})$). Then there are a sheaf of commutative $A$-algebras on the relative
prismatic site of $X$, an identification of its underlying sheaf of modules with the structure
sheaf $\mathcal{O}_\Delta$, and a map to it from the structure presheaf of algebras through which
this identification is the sheafification unit (`StructuralAlgebra`). -/
public def_wanted structuralAlgebra
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) : StructuralAlgebra p P X

/-- A hyperresolution of the prismatic structure sheaf by sheaves of algebras: let $p$ be a prime,
$(A, I)$ a bounded prism and $X$ a $p$-adic formal scheme over $\operatorname{Spf}(A/I)$
(`FormalScheme`, with levels over $A/(I+(p)^{n+1})$), whose derived global sections functor exists
(`HasDerivedSections`), and $O$ a structure algebra sheaf for $X$ (`StructuralAlgebra`). Then there
is a cosimplicial sheaf of commutative algebras augmented by $O$ whose alternating coface complex of
modules is a resolution of $\mathcal{O}_\Delta$ on which derived global sections are computed
termwise, with its complex of global sections identified with that of the global algebras
(`Hypermodel`). -/
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

/-- Compatible algebra hyperresolutions along a base change: let $p$ be a prime, $(A, I) \to (B, J)$
a map of bounded prisms and $g : Y \to X$ a map from a $p$-adic formal scheme over
$\operatorname{Spf}(B/J)$ to one over $\operatorname{Spf}(A/I)$, over the induced map of formal
spectra (`PrismaticBaseChangeMaps.Map`), with derived global sections functors on both relative
prismatic sites, and $O$, $V$ structure algebra sheaves for $X$ and $Y$ (`StructuralAlgebra`). Then
there are hyperresolutions $H$ of $O$ and $K$ of $V$ by sheaves of algebras (`Hypermodel`), together
with ring maps from the sections of $H$ over the image of each object to the sections of $K$,
compatible with scalars, restrictions, the cosimplicial structure and the augmentations
(`SiteAlgebraMap`). -/
public def_wanted baseChangeHypermodels
    (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) (Y : FormalScheme p Q.ring Q.ideal)
    [HasDerivedSections p P X] [HasDerivedSections p Q Y]
    (g : MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps.Map p P Q X Y)
    (O : StructuralAlgebra p P X) (V : StructuralAlgebra p Q Y) :
    Σ H : Hypermodel p P X O, Σ K : Hypermodel p Q Y V,
      SiteAlgebraMap p P Q X Y g H K

/-- Prismatic cohomology is derived complete: let $p$ be a prime, $(A, I)$ a bounded prism and $X$ a
$p$-adic formal scheme over $\operatorname{Spf}(A/I)$ whose $n$-th level is smooth over
$A/(I+(p)^{n+1})$ for every $n$, with a derived global sections functor (`HasDerivedSections`).
Then the relative prismatic cohomology $R\Gamma_\Delta(X/A)$ is derived $(p, I)$-complete. -/
public theorem_wanted prismaticIsComplete
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) [HasDerivedSections p P X]
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) :
    IsComplete P.ring (completionIdeal p P.ideal) (prismatic p P X)

/-- Base change for prismatic cohomology (Bhatt–Scholze, Corollary 4.12): let $p$ be a prime,
$(A, I) \to (B, J)$ a map of bounded prisms and $g : Y \to X$ a map from a $p$-adic formal scheme
over $\operatorname{Spf}(B/J)$ to one over $\operatorname{Spf}(A/I)$, over the induced map of formal
spectra (`PrismaticBaseChangeMaps.Map`), such that derived scalar extension along $A \to B$ exists
(`HasExtension`), $g$ is Cartesian at every level, $X$ is smooth, quasi-compact and quasi-separated
at every level, and both relative prismatic sites have derived global sections functors. Fix
structure algebra sheaves with compatible hyperresolutions $H$, $K$ and a map between them
(`SiteAlgebraMap`), algebra structures on their global cochains with an algebra map realizing it
(`AlgebraMap`), and a derived $(p, J)$-completion functor on $B$-modules, and assume the global
cochains of $K$ derived $(p, J)$-complete. Then the induced map from the completed base change
$R\Gamma_\Delta(X/A) \hat{\otimes}^L_A B$ to $R\Gamma_\Delta(Y/B)$ is an isomorphism. The
quasi-compactness and quasi-separatedness hypotheses are needed: for a countable disjoint union of
copies of the base, the completed tensor product does not commute with the infinite product of
global sections. -/
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
