/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PrismaticSyntomicModels

/-!
# Actual Nygaard, Breuil--Kisin and syntomic construction requests

Initial prism maps, finite quotient rings, tensor/dual words, conormal
period generators, inverse-Frobenius scalars, projection-normalized
coordinate maps and phi-can fibers are fixed in MathlibExt.

Line and Frobenius dictionaries are constructed jointly, with their
actual quasisyntomic coordinate covers. These requests do not assert
that arbitrary independently chosen finite line comparisons admit a
compatible Frobenius. Invertibility stays on finite filtered quotients.

References: BMS arXiv:1802.03261v2, Theorem 1.12(3)--(5),
Proposition 6.5, Remark 6.6 and Section 7.4; BMS18
arXiv:1602.03148v3, Example 4.24; Bhatt--Scholze
arXiv:1905.08229v4, Theorems 1.12--1.14.
Relative phi_A/qSyn normalization and geometric nearby-cycle
comparisons are separate endpoints, not assumed by these constructors.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PrismaticNygaardTwists

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.AlgebraicGeometry.AbsolutePrismaticBasis
open MathlibExt.AlgebraicGeometry.QuasiSyntomicPrismSites
open MathlibExt.AlgebraicGeometry.PrismaticBreuilKisinSeeds
open MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames
open MathlibExt.AlgebraicGeometry.PrismaticFilteredTwists
open MathlibExt.AlgebraicGeometry.PrismaticSyntomicModels

attribute [local instance] HasDerivedCategory.standard

/-- Construct a genuine quasiregular semiperfectoid covering ring. -/
public def_wanted semiperfectoidCover
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p) :
    SemiperfectoidCover p A

/-- Initial absolute prisms on the actual quasisyntomic basis. -/
public def_wanted initialBasisPrisms
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p) :
    ∀ B : Basis p A, AbsolutePrismaticBasis.InitialLift p (ring p B)

/-- Normalize the actual zero Nygaard quotient by its Frobenius-residue image. -/
public def_wanted zeroNygaardReduction
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    (D : ∀ B : Basis p A, AbsolutePrismaticBasis.InitialLift p (ring p B)) :
    ZeroReduction p A D

/-- The source's classical p-torsionfree perfectoid conormal seed and theta reduction. -/
public def_wanted classicalBreuilKisinSeed
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (hPerfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (hTorsionFree : Function.Injective (fun x : P.Residue ↦ (p : P.Residue) * x)) :
    ClassicalSeed p P

/-- The standard cyclotomic xi has the source's actual conormal transition congruence. -/
public theorem_wanted periodGeneratorCongruence
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (hPerfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (epsilon : P.ring) (hUnit : IsUnit epsilon)
    (hTeichmuller : DeltaRing.frobenius p P.ring epsilon = epsilon ^ p)
    (hTheta : Ideal.Quotient.mk P.ideal epsilon = 1)
    (hIdeal : P.ideal = Ideal.span {xi p P hPerfect epsilon}) :
    ∀ n : ℕ, phiPower p P (n + 2) (xi p P hPerfect epsilon) - (p : P.ring) ∈ periodIdeal p P n

/-- The actual compatible conormal generator gives the source period-module frame. -/
public theorem_wanted periodFrameIsIso
    (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
    (hPerfect : Function.Bijective (DeltaRing.frobenius p P.ring))
    (L : ClassicalSeed p P) (G : Generator p P hPerfect) :
    IsIso (frameHom p P hPerfect L G)

/-- Construct compatible finite filtered lines and their actual coordinate-normalized Frobenius,
jointly with the vanishing of the negative syntomic fibres after quasisyntomic cohomology. The
coordinate normalization does not determine the Frobenius (see `FrobeniusModel`), so this property
is requested for the model chosen here rather than for every Frobenius model. -/
public def_wanted bmsTwistFrobeniusModels
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    [MathlibExt.AlgebraicGeometry.PrismaticNygaardCohomology.HasDerivedSections p A]
    (D : ∀ B : Basis p A, AbsolutePrismaticBasis.InitialLift p (ring p B))
    (Z : ZeroReduction p A D) :
    Σ T : TwistTower p A D Z,
      {F : FrobeniusModel p A D Z T // ∀ i : ℤ, i < 0 → IsZero (F.global i)}

/-- These actual syntomic global objects are derived p-complete integer complexes, for every
Frobenius model (derived completeness is preserved by fibres, whatever the Frobenius). -/
public theorem_wanted syntomicIsPComplete
    (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
    [MathlibExt.AlgebraicGeometry.PrismaticNygaardCohomology.HasDerivedSections p A]
    (D : ∀ B : Basis p A, AbsolutePrismaticBasis.InitialLift p (ring p B))
    (Z : ZeroReduction p A D) (T : TwistTower p A D Z)
    (F : FrobeniusModel p A D Z T) (i : ℤ) :
    IsComplete ℤ (Ideal.span {(p : ℤ)}) (F.global i)

end WantedExt.AlgebraicGeometry.PrismaticNygaardTwists
