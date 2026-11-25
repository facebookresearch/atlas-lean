/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LargeQuasiSyntomicAlgebras
public import MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Actual absolute and relative quasisyntomic sites

Absolute objects are p-complete rings with bounded p-infinity torsion
and the native cotangent Tor-amplitude condition over Z_p. No flatness
over Z_p is imposed on an absolute object. Relative quasisyntomic maps
have actual complete-flat Tor and relative cotangent conditions.
Covers are faithfully flat on every positive p-power quotient.

The relative site is the genuine category of such algebras under a fixed
ring, in its geometric opposite. Semiperfectoid covering data retain
actual perfect base prisms and surjective residue maps; they contain no
syntomic, nearby-cycle or comparison theorem.

References: BMS arXiv:1802.03261v2, Definitions 4.10, 4.13 and 4.20,
Lemmas 4.28 and 4.30; Bhatt--Scholze arXiv:1905.08229v4,
Theorems 1.12 and 1.14. Polynomial/cotangent and tensor operations use
the completed native source adapters already imported.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QuasiSyntomicPrismSites

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open LargeQuasiSyntomicAlgebras GeometricCotangentComplex PrismaticNygaardModels

variable (p : ℕ) [Fact p.Prime]

/-- The source's absolute quasisyntomic ring, on actual p-complete ring objects. -/
structure Ring where
  algebra : CommAlgCat.{0} (PadicInt p)
  [tensor : HasTensor algebra]
  complete : IsCompleteRing algebra (Ideal.span {(p : algebra)})
  bounded : ∃ N : ℕ, ∀ (x : algebra) (n : ℕ),
    (p : algebra) ^ n * x = 0 → (p : algebra) ^ N * x = 0
  resolution : PolynomialResolution (PadicInt p) algebra
  amplitude : HasPadicCotangentAmplitude p (PadicInt p) algebra resolution

attribute [instance] Ring.tensor

instance : Category (Ring p) where
  Hom U V := U.algebra →ₐ[PadicInt p] V.algebra
  id U := AlgHom.id _ _
  comp f g := g.comp f
  id_comp _ := by ext x; rfl
  comp_id _ := by ext x; rfl
  assoc _ _ _ := by ext x; rfl

/-- The actual coefficient map on every finite p-power quotient. -/
def scalarQuotient {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (m : ℕ) :
    (A ⧸ Ideal.span {(p : A) ^ m}) →+* (B ⧸ Ideal.span {(p : B) ^ m}) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp f) (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have h : (Ideal.span {(p : A) ^ m}).map f = Ideal.span {(p : B) ^ m} := by
        rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
      rw [← h]
      exact Ideal.mem_map_of_mem f hx)

/-- Relative quasisyntomicity is on the actual displayed ring map and cotangent source. -/
structure QuasiMap (U V : Ring p) (f : U ⟶ V) where
  flat : letI := f.toRingHom.toAlgebra
    IsPCompletelyFlat p U.algebra V.algebra
  resolution : letI := f.toRingHom.toAlgebra
    PolynomialResolution U.algebra V.algebra
  amplitude : letI := f.toRingHom.toAlgebra
    HasPadicCotangentAmplitude p U.algebra V.algebra resolution

/-- The real covering condition, with no positive p-power quotient omitted. -/
def IsCover {U V : Ring p} (f : U ⟶ V) : Prop :=
  Nonempty (QuasiMap p U V f) ∧
  ∀ m : ℕ, letI := (scalarQuotient p f.toRingHom (m + 1)).toAlgebra
    Module.FaithfullyFlat
      (U.algebra ⧸ Ideal.span {(p : U.algebra) ^ (m + 1)})
      (V.algebra ⧸ Ideal.span {(p : V.algebra) ^ (m + 1)})

/-- Genuine relative quasisyntomic algebras under the specified ring. -/
abbrev Relative (A : Ring p) :=
  (show ObjectProperty (Under A) from
    fun B ↦ Nonempty (QuasiMap p A B.right B.hom)).FullSubcategory

/-- The actual relative quasisyntomic covering topology in the geometric direction. -/
def topology (A : Ring p) : GrothendieckTopology (Relative p A)ᵒᵖ :=
  sInf {J | ∀ (U V : Relative p A) (f : U ⟶ V),
    IsCover p f.hom.right →
      Sieve.ofArrows (fun _ : Unit ↦ op V) (fun _ ↦ f.op) ∈ J (op U)}

/-- A quasiregular semiperfectoid cover retains its real base, residue and initial prism. -/
structure SemiperfectoidCover (A : Ring p) where
  ring : Ring p
  map : A ⟶ ring
  cover : IsCover p map
  base : Prism.{0} p
  perfect : Function.Bijective (MathlibExt.RingTheory.DeltaRing.frobenius p base.ring)
  residueMap : base.Residue →+* ring.algebra
  surjective : Function.Surjective residueMap
  initial : letI := residueMap.toAlgebra
    InitialLift p base ring.algebra

end MathlibExt.AlgebraicGeometry.QuasiSyntomicPrismSites
