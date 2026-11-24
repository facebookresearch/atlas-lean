/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.FormalDeRhamModels

/-!
# General bounded-prism and formal de Rham construction requests

The completed cores fix actual delta rings, locally Cartier ideals,
localization-derived-Hom completeness, nilpotent formal scheme diagrams,
completely flat Tor covers, structural module sheaves and derived sections.
The de Rham target is a literal Milnor fiber of generator-normalized
form hypermodels. Generic derived and ordinary differential constructors
remain explicit source-integration inputs, never replacement carriers.

The comparison below is the underlying derived-module component of
Bhatt--Scholze, arXiv:1905.08229v4, Theorem 1.8(3), requested for quasi-compact and
quasi-separated formal schemes, since it extends scalars through global sections. Its
algebra/unit/cup
enhancement is a separate normalized interface; a module isomorphism is
not labelled a commutative-algebra comparison. The rigidity request is
Lemma 3.5. Formal hypermodels use the actual ordinary de Rham source and
the injective comparison construction of Stacks, Tag 070A.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralPrismaticComparison

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry.PadicFormalSchemes
open MathlibExt.AlgebraicGeometry.FormalDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativePrismaticCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Actual bounded-prism maps identify the base-changed Cartier ideal. -/
public theorem_wanted idealBaseChange
    (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p) (f : P ⟶ Q) :
    P.ideal.map f.hom = Q.ideal

/-- Normalize ordinary form hypermodels and their actual restriction
maps on the specified formal nilpotent presentation. -/
public def_wanted formalDeRhamModels
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal) : System p P X

/-- The underlying derived-module comparison along the actual phi_A
quotient map, for an arbitrary bounded prism and a smooth, quasi-compact and quasi-separated
formal scheme (Bhatt–Scholze, Thm. 1.8(3)). The scalar extension is applied to global sections,
so the qcqs hypothesis is needed: for a countable disjoint union of copies of the base over a
square-zero crystalline prism it creates a nonzero `H⁻¹`, which de Rham cohomology does not
have. -/
public theorem_wanted deRhamModuleComparison
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (X : FormalScheme p P.ring P.ideal)
    [HasDerivedSections p P X] [HasExtension (deRhamScalars p P)]
    (C : Completion P.Residue (Ideal.span {(p : P.Residue)}))
    (S : System p P X)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (hQcqs : ∀ n : ℕ, QuasiCompact (X.structureMap.app n) ∧
      QuasiSeparated (X.structureMap.app n)) :
    Nonempty (deRhamSpecialization p P X C ≅ S.derived)

end WantedExt.AlgebraicGeometry.GeneralPrismaticComparison
