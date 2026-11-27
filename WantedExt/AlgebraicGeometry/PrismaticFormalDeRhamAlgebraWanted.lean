/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrismaticFormalDeRhamAlgebraMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Actual formal de Rham algebra and comparison construction requests

The wedge, resolution square, global-section products and both Milnor-fiber
coordinates are fixed independently of the geometric prismatic comparison.
Compatible multiplicative hypermodels and their comparison are constructed
jointly. The map uses the actual phi_A quotient scalar map, preserves all
prescribed cups/units and is normalized by the native completion unit. The comparison is
requested for quasi-compact and quasi-separated formal schemes.

References: Bhatt–Scholze, arXiv:1905.08229v4, Theorem 1.8(3) and
Corollary 15.4; Stacks Project, Tags 070A and 091Z.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PrismaticFormalDeRhamAlgebra

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.AlgebraicGeometry
open PadicFormalSchemes RelativeDeRhamModels RelativeDeRhamWedgeModels
open FormalDeRhamModels FormalDeRhamCupModels PrismaticAlgebraHypermodels
open PrismaticCosimplicialAlgebras RelativePrismaticCohomology

attribute [local instance] HasDerivedCategory.standard

public def_wanted relativeWedgeAssembly
    (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
    (D : RelativeDeRhamModels.Differential R X) : WedgeAssembly R X D

public def_wanted formalAlgebraHypermodels
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (X : FormalScheme p P.ring P.ideal) :
    Σ S : System p P X, Σ H : HypermodelAlgebra p P X S, FormalAlgebra p P X S H

public theorem_wanted formalDeRhamIsPComplete
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (X : FormalScheme p P.ring P.ideal)
    (S : System p P X) : IsComplete P.Residue (Ideal.span {(p : P.Residue)}) S.derived

/-- **The de Rham comparison for prismatic cohomology, as algebras.** Let $p$ be a prime, $(A, I)$ a
bounded prism and $X$ a $p$-adic formal scheme over $A/I$ whose levels $X_n$ are smooth,
quasi-compact and quasi-separated over $A/(I + (p)^{n+1})$. Assume that derived global sections on
its prismatic site and derived base change along $A → A/I$, $a ↦ φ(a) \bmod I$, exist, and let `O`
be the given structural algebra and `C` a chosen derived $p$-completion on $A/I$-modules. Then there
are an algebra hyperresolution of `O` (`Hypermodel`) with an algebra structure on its global
sections, multiplicative hyperresolutions of the de Rham complex of $X$ (`System`,
`HypermodelAlgebra`) with their formal de Rham algebra (`FormalAlgebra`), and a map of cochain
algebras from the first to the second along $a ↦ φ(a) \bmod I$, preserving products and units, such
that the formal de Rham complex is derived $p$-complete and the induced map to it from the
$p$-completed base change of the prismatic cohomology is an isomorphism (Bhatt–Scholze,
Theorem 1.8(3) and Corollary 15.4). The base change is applied to global sections, which is why $X$
is assumed quasi-compact and quasi-separated. -/
public def_wanted prismaticDeRhamAlgebraComparison
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p) (X : FormalScheme p P.ring P.ideal)
    [RelativePrismaticCohomology.HasDerivedSections p P X]
    [HasExtension (deRhamScalars p P)]
    (O : StructuralAlgebra p P X)
    (C : Completion P.Residue (Ideal.span {(p : P.Residue)}))
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (hQcqs : ∀ n : ℕ, QuasiCompact (X.structureMap.app n) ∧
      QuasiSeparated (X.structureMap.app n)) :
    Σ H : Hypermodel p P X O,
      Σ M : AlgebraAssembly H.globalDiagram,
        Σ S : System p P X,
          Σ Q : HypermodelAlgebra p P X S,
            Σ F : FormalAlgebra p P X S Q,
              Σ a : PrismaticFormalDeRhamAlgebraMaps.Map p P X H M S F,
                (h : IsComplete P.Residue (Ideal.span {(p : P.Residue)}) S.derived) ×'
                  IsIso (a.completed C h)

end WantedExt.AlgebraicGeometry.PrismaticFormalDeRhamAlgebra
