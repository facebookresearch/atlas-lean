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

/-- A Frobenius on the Nygaard-completed twists `T`: maps of complexes $\varphi_i$ from
`T.nygaard i` to `T.complex i`, for $i \in \mathbb{Z}$, such that every basis object $B$ has a
morphism $B \to C$ to a basis object $C$ with coordinates (`Context`) whose ring map is a
quasisyntomic cover, together with, for every basis object with coordinates `F` and every $i$, a
realization of the coordinate complexes (`Realization`) whose source map followed by $\varphi_i$
(evaluated at the basis object) is homotopic to the signed divided Frobenius `phiSigned` of the
coordinates followed by its target map.

These conditions constrain $\varphi_i$ only through its composites with the source maps of the
realizations, which are defined on the uncompleted coordinate complexes (the Nygaard steps of the
initial prism), whereas `T.nygaard i` and `T.complex i` are Nygaard-completed. -/
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
