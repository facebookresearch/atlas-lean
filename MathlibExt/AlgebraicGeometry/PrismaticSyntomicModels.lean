/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticSyntomicCoordinates

/-!
# Source-normalized completed syntomic fibers

The complete signed twist and every Nygaard inclusion are actual
finite-quotient/Milnor constructions. Frobenius construction output is
fixed on source period-frame coordinates by the literal delta divided
Frobenius, on a genuine quasisyntomic covering family at every basis
object. Every coordinate map is constrained by all finite projections.

Both maps are integer-linear cochain maps. Syntomic cochains are exactly
cone(phi-can)[-1], and finite coefficients are the actual cone of p^r.
No A-linear subtraction of a semilinear Frobenius is made.

Compatible line/Frobenius models must be constructed together; no
existence statement is made for an arbitrary incoherent line dictionary.
References: BMS arXiv:1802.03261v2, Theorem 1.12(3)--(5) and Section 7.4;
BMS18 arXiv:1602.03148v3, Example 4.24.
The E-infinity background, qsyn/prismatic normalization and geometric
nearby-cycle comparison remain separate explicit construction/theorem
dependencies.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticSyntomicModels

open CategoryTheory CategoryTheory.Limits Opposite
open AbsolutePrismaticBasis PrismaticFilteredTwists
open PrismaticSyntomicCoordinates PrismaticDividedFrobenius

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))
  (Z : ZeroReduction p A D) (T : TwistTower p A D Z)

/-- Completed Frobenius is construction output normalized on actual source coordinates.
The covering requirement keeps these normalization tests nonvacuous on every basis object.

The normalization pins the evaluated Frobenius only on the image of the uncompleted coordinates
`N^{≥i}Δ_S → Δ_S`; the complexes `T.nygaard i` and `T.complex i` are Nygaard-completed, and the
continuous extension (from the Nygaard topology to the `(p, I)`-adic one) that determines it on
the completion is not encoded. So a `FrobeniusModel` is not unique, and statements that depend on
the choice of Frobenius are requested for a model chosen jointly with them. -/
structure FrobeniusModel where
  phi : ∀ i : ℤ, T.nygaard i ⟶ T.complex i
  coordinateCover : ∀ B : Basis p A, ∃ (C : Basis p A) (f : B ⟶ C),
    QuasiSyntomicPrismSites.IsCover p (ringMap p f) ∧
      Nonempty (Context p A D (op (op C)))
  realization : ∀ (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (F : Context p A D B) (i : ℤ),
    Realization p A D Z T B F i
  normalization : ∀ (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (F : Context p A D B) (i : ℤ),
    Homotopy
      ((realization B F i).source ≫
        ((evaluate p A B).mapHomologicalComplex (ComplexShape.up ℤ)).map (phi i))
      (phiSigned p (D B.unop.unop).lift.prism.ring F.divisor F.regular i ≫
        (realization B F i).target)

namespace FrobeniusModel

variable {p A D Z T} (F : FrobeniusModel p A D Z T)

/-- The source's actual phi-minus-can map on the same integer-coefficient objects. -/
def difference (i : ℤ) : T.nygaard i ⟶ T.complex i := F.phi i - T.can i

/-- Literal completed syntomic sheaf cochains, with the homotopy-fiber shift. -/
def syntomic (i : ℤ) :
    CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  CochainComplex.mappingCocone (F.difference i)

/-- Actual derived mod-p^r coefficients, preserving torsion and the cone shift. -/
def modp (i : ℤ) (r : ℕ) :
    CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ :=
  CochainComplex.mappingCone ((p ^ r : ℤ) • (𝟙 (F.syntomic i)))

/-- Quasisyntomic global cohomology of the actual syntomic fiber. -/
def global [PrismaticNygaardCohomology.HasDerivedSections p A] (i : ℤ) :
    DerivedCategory (ModuleCat.{1} ℤ) :=
  (PrismaticNygaardCohomology.derivedSections p A).obj
    (DerivedCategory.Q.obj (F.syntomic i))

/-- Actual finite-level quasisyntomic global cohomology. -/
def finiteGlobal [PrismaticNygaardCohomology.HasDerivedSections p A] (i : ℤ) (r : ℕ) :
    DerivedCategory (ModuleCat.{1} ℤ) :=
  (PrismaticNygaardCohomology.derivedSections p A).obj
    (DerivedCategory.Q.obj (F.modp i r))

end FrobeniusModel

end MathlibExt.AlgebraicGeometry.PrismaticSyntomicModels
