/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Minimal graded resolutions over polynomial rings

The free terms are actual finite free modules with integer degree shifts.
Exactness uses the kernels and ranges of actual polynomial-linear maps.
Minimality means the differential has image in the irrelevant ideal times
the target free module, rather than an arbitrary minimality predicate.

Reference: Eisenbud, *Commutative Algebra with a View Toward Algebraic
Geometry*, Chapter 20, https://doi.org/10.1007/978-1-4612-5350-1.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.MinimalGradedResolution

variable {k : Type*} [Field k] {n : ℕ}

abbrev PolynomialRing (k : Type*) [Field k] (n : ℕ) := MvPolynomial (Fin n) k

/-- The standard polynomial grading, extended to integer degrees. -/
def polynomialPiece (j : ℤ) : Submodule k (PolynomialRing k n) :=
  MvPolynomial.weightedHomogeneousSubmodule k (fun _ ↦ (1 : ℤ)) j

/-- The irrelevant homogeneous ideal. -/
def irrelevant : Ideal (PolynomialRing k n) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin n → PolynomialRing k n))

/-- A degree piece of a finite direct sum of shifted copies of the ring. -/
def freePiece {b : ℕ} (degrees : Fin b → ℤ) (j : ℤ) :
    Submodule k (Fin b → PolynomialRing k n) where
  carrier := {f | ∀ i, f i ∈ polynomialPiece (j - degrees i)}
  zero_mem' i := (polynomialPiece (j - degrees i)).zero_mem
  add_mem' hf hg i := (polynomialPiece (j - degrees i)).add_mem (hf i) (hg i)
  smul_mem' a _f hf i := (polynomialPiece (j - degrees i)).smul_mem a (hf i)

variable {M : Type*} [AddCommGroup M] [Module (PolynomialRing k n) M]
  [Module k M] [IsScalarTower k (PolynomialRing k n) M]

/-- A genuine grading of a module, including compatibility with the polynomial action. -/
structure Grading where
  piece : ℤ → Submodule k M
  isInternal : DirectSum.IsInternal piece
  smul_mem : ∀ a b, ∀ p ∈ polynomialPiece (k := k) (n := n) a,
    ∀ m ∈ piece b, p • m ∈ piece (a + b)
  boundedBelow : ∃ B : ℤ, ∀ j < B, piece j = ⊥

/-- A minimal graded free resolution of the specified module and grading. -/
structure MinimalResolution (G : Grading (k := k) (n := n) (M := M)) where
  ranks : ℕ → ℕ
  degrees : ∀ i, Fin (ranks i) → ℤ
  differential : ∀ i,
    (Fin (ranks (i + 1)) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (ranks i) → PolynomialRing k n)
  augmentation :
    (Fin (ranks 0) → PolynomialRing k n) →ₗ[PolynomialRing k n] M
  differential_graded : ∀ i j, ∀ x ∈ freePiece (degrees (i + 1)) j,
    differential i x ∈ freePiece (degrees i) j
  augmentation_graded : ∀ j, ∀ x ∈ freePiece (degrees 0) j,
    augmentation x ∈ G.piece j
  augmentation_surjective : Function.Surjective augmentation
  exact_zero : LinearMap.range (differential 0) = LinearMap.ker augmentation
  exact_succ : ∀ i,
    LinearMap.range (differential (i + 1)) = LinearMap.ker (differential i)
  minimal : ∀ i,
    LinearMap.range (differential i) ≤
      irrelevant (k := k) (n := n) • (⊤ : Submodule (PolynomialRing k n)
        (Fin (ranks i) → PolynomialRing k n))
  length_bound : ∀ i, n < i → ranks i = 0

/-- Actual counts of degree shifts in a minimal free term. -/
def betti (G : Grading (k := k) (n := n) (M := M))
    (P : MinimalResolution G) (i : ℕ) (j : ℤ) : ℕ :=
  (Finset.univ.filter fun a ↦ P.degrees i a = j).card

end MathlibExt.RingTheory.MinimalGradedResolution
