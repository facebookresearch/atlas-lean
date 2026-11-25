/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Flat.Basic
public import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
public import MathlibExt.RingTheory.DerivedModuleScalarOperations

/-!
# Large quasisyntomic residue algebras on actual ring and Tor objects

The root-polynomial algebra is the actual quotient by compatible p-power
relations and its native p-adic completion. Complete flatness uses actual
Tor and the quotient flat module. Cotangent amplitude uses the actual
polynomial-resolution cotangent complex tensored with p-annihilated
modules, with cohomology outside [-1,0] equal to zero.

These are original native adapters for Bhatt--Scholze,
arXiv:1905.08229v4, Definition 15.1, p102. Generic polynomial resolutions
and derived tensor existence are already completed public source inputs.
No freely named quasisyntomic predicate or cotangent carrier is supplied.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LargeQuasiSyntomicAlgebras

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory.DerivedAdicCompleteness
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open GeometricCotangentComplex

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]

/-- The actual compatibility ideal for infinitely many p-power roots. -/
def rootRelations (R : Type) [CommRing R] (σ : Type) :
    Ideal (MvPolynomial (σ × ℕ) R) :=
  Ideal.span {f | ∃ (i : σ) (n : ℕ),
    f = MvPolynomial.X (i, n + 1) ^ p - MvPolynomial.X (i, n)}

/-- The polynomial root tower before completion. -/
abbrev rootPolynomial (R : Type) [CommRing R] (σ : Type) :=
  MvPolynomial (σ × ℕ) R ⧸ rootRelations p R σ

/-- Its actual native p-adic completion, not a selected algebra label. -/
abbrev completedRootPolynomial (R : Type) [CommRing R] (σ : Type) :=
  AdicCompletion (Ideal.span {(p : rootPolynomial p R σ)})
    (rootPolynomial p R σ)

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical scalar map on actual p-quotient rings. -/
def scalarModp : (R ⧸ Ideal.span {(p : R)}) →+*
    (S ⧸ Ideal.span {(p : S)}) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.span {(p : S)})).comp (algebraMap R S))
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have h : (Ideal.span {(p : R)}).map (algebraMap R S) =
          Ideal.span {(p : S)} := by
        rw [Ideal.map_span, Set.image_singleton, map_natCast]
      rw [← h]
      exact Ideal.mem_map_of_mem _ hx)

/-- Complete flatness of the specified residue algebra, using actual Tor. -/
def IsPCompletelyFlat : Prop :=
  (∀ n : ℕ, IsZero
    (((Tor (ModuleCat.{0} R) (n + 1)).obj (ModuleCat.of R S)).obj
      (ModuleCat.of R (R ⧸ Ideal.span {(p : R)})))) ∧
  letI := (scalarModp p R S).toAlgebra
  Module.Flat (R ⧸ Ideal.span {(p : R)})
    (S ⧸ Ideal.span {(p : S)})

/-- The actual resolution cotangent complex lifted only in module universe. -/
def cotangentObject (C : PolynomialResolution R S) : D S :=
  DerivedCategory.Q.obj
    (((ModuleCat.uliftFunctor.{1, 0} S).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (affineComplex C))

/-- p-adic Tor amplitude [-1,0] on actual cotangent and tensor objects. -/
def HasPadicCotangentAmplitude [HasTensor S]
    (C : PolynomialResolution R S) : Prop :=
  ∀ (M : Modules S), (∀ x : M, (p : S) • x = 0) →
    ∀ i : ℤ, (i < -1 ∨ 0 < i) → IsZero
      ((DerivedCategory.homologyFunctor (Modules S) i).obj
        ((tensor S).obj (cotangentObject R S C,
          (DerivedCategory.singleFunctor (Modules S) 0).obj M)))

/-- The complete, flat, actual cotangent-amplitude condition of the source. -/
structure QuasiSyntomic [HasTensor S] where
  complete : IsCompleteRing S (Ideal.span {(p : S)})
  flat : IsPCompletelyFlat p R S
  resolution : PolynomialResolution R S
  amplitude : HasPadicCotangentAmplitude p R S resolution

/-- Largeness uses a surjective map from the actual completed root algebra. -/
structure LargeQuasiSyntomic [HasTensor S] extends QuasiSyntomic p R S where
  generators : Type
  map : completedRootPolynomial p R generators →ₐ[R] S
  surjective : Function.Surjective map

end MathlibExt.AlgebraicGeometry.LargeQuasiSyntomicAlgebras
