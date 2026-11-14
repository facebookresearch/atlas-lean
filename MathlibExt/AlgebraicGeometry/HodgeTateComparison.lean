/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The closure-norm proof is adapted from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/NumberTheory/Padics/AlgebraicClosure.lean, AlgEquiv.norm_apply.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: The Tau Ceti contributors.
Modification: retain the norm/isometry argument and use Mathlib's actual
completion ring-equivalence construction to obtain the C_p Galois action.
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Actual carriers and actions for Hodge–Tate comparison

The left side is C_p tensored with actual continuous rational pro-étale
cohomology of the geometric scheme fibre. The right side is a finite
product of C_p tensored with actual coherent cohomology of the constructed
algebraic differential-form sheaves. Tate twists use Mathlib's constructed
cyclotomic character, characterized by its actual roots-of-unity action.

Galois acts on C_p by completing its actual norm-preserving action on
the algebraic closure. It acts on étale cohomology by the fixed scheme
operator from `GeometricAdicGaloisOperators`. These actions are complete
code; the geometric comparison is a separate construction.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeometricAdicGaloisOperators AdicLinearFunctoriality
open CoherentCurveLinearSeries
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

abbrev Galois := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/-- Galois preserves the actual spectral norm on the algebraic closure. -/
theorem closure_norm_apply (σ : Galois p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem closure_isometry (σ : Galois p) : Isometry σ := by
  refine isometry_iff_dist_eq.mpr fun x y => ?_
  rw [dist_eq_norm, ← map_sub σ, closure_norm_apply, dist_eq_norm]

/-- Complete the actual field automorphism, fixing Q_p. -/
def completionGalois (σ : Galois p) :
    PadicComplex p ≃ₐ[ℚ_[p]] PadicComplex p := by
  let e : PadicComplex p ≃+* PadicComplex p :=
    UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
      (closure_isometry p σ).continuous (closure_isometry p σ.symm).continuous
  refine AlgEquiv.ofBijective
    ({ toRingHom := e.toRingHom
       commutes' := ?_ } : PadicComplex p →ₐ[ℚ_[p]] PadicComplex p)
    e.bijective
  intro r
  change UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
      (closure_isometry p σ).continuous
      ((algebraMap ℚ_[p] (PadicAlgCl p) r : PadicAlgCl p) :
        PadicComplex p) = algebraMap ℚ_[p] (PadicComplex p) r
  exact (UniformSpace.Completion.mapRingHom_coe
    (f := σ.toRingEquiv.toRingHom) (closure_isometry p σ).continuous
    (algebraMap ℚ_[p] (PadicAlgCl p) r)).trans
      (congrArg (algebraMap (PadicAlgCl p) (PadicComplex p)) (σ.commutes r))

/-- The completed action is fixed on every algebraic-closure element. -/
theorem completionGalois_coe (σ : Galois p) (x : PadicAlgCl p) :
    completionGalois p σ (algebraMap (PadicAlgCl p) (PadicComplex p) x) =
      algebraMap (PadicAlgCl p) (PadicComplex p) (σ x) :=
  UniformSpace.Completion.mapRingHom_coe
    (f := σ.toRingEquiv.toRingHom) (closure_isometry p σ).continuous x

/-- The coefficient is the actual p-adic cyclotomic character. -/
def cyclotomicScalar (σ : Galois p) : ℚ_[p] :=
  algebraMap ℤ_[p] ℚ_[p]
    (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val

theorem cyclotomicScalar_ne_zero (σ : Galois p) :
    cyclotomicScalar p σ ≠ 0 :=
  ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).isUnit.map
    (algebraMap ℤ_[p] ℚ_[p])).ne_zero

/-- The coefficient of the negative Tate twist C_p(-i). -/
def tateScalar (σ : Galois p) (i : ℕ) : ℚ_[p] :=
  cyclotomicScalar p σ ^ (-(i : ℤ))

variable (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))

abbrev Etale (n : ℕ) :=
  AdicCohomology p (geometricFibre X (PadicAlgCl p)) n

abbrev CompletedEtale (n : ℕ) :=
  PadicComplex p ⊗[ℚ_[p]] Etale p X n

/-- Hodge cohomology is the actual right-derived global-section module. -/
abbrev Hodge (n i : ℕ) :=
  cohomology X.hom (AlgebraicDifferentialSheaves.forms ℚ_[p] X i) (n - i)

/-- A finite product realizes the direct sum of cohomological Hodge pieces. -/
abbrev CompletedHodge (n : ℕ) :=
  ∀ i : Fin (n + 1), PadicComplex p ⊗[ℚ_[p]] Hodge p X n i

/-- This is the actual Q_p-linear scheme-cohomology operator. -/
def etaleGalois (σ : Galois p) (n : ℕ) :
    Etale p X n →ₗ[ℚ_[p]] Etale p X n :=
  continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
    (galoisSchemeOperator X (PadicAlgCl p) σ) n

theorem etaleGalois_apply (σ : Galois p) (n : ℕ) (a : Etale p X n) :
    etaleGalois p X σ n a =
      galoisCohomologyOperator X (PadicAlgCl p) p σ n a := rfl

/-- The diagonal action uses the actual two factors' operators. -/
def completedEtaleGalois (σ : Galois p) (n : ℕ) :
    CompletedEtale p X n →ₗ[ℚ_[p]] CompletedEtale p X n :=
  TensorProduct.map (completionGalois p σ).toLinearMap (etaleGalois p X σ n)

/-- Galois acts on Hodge degree i by its actual C_p action and χ^(-i). -/
def completedHodgeGalois (σ : Galois p) (n : ℕ) :
    CompletedHodge p X n →ₗ[ℚ_[p]] CompletedHodge p X n :=
  LinearMap.pi fun i =>
    (TensorProduct.map
      (tateScalar p σ i • (completionGalois p σ).toLinearMap)
      (LinearMap.id : Hodge p X n i →ₗ[ℚ_[p]] Hodge p X n i)).comp
        (LinearMap.proj i)

/-- A geometric comparison on the actual carriers, with all Galois
operators fixed before the comparison is supplied. -/
structure Comparison (n : ℕ) where
  equivalence : CompletedEtale p X n ≃ₗ[PadicComplex p] CompletedHodge p X n
  equivariant : ∀ (σ : Galois p) (a : CompletedEtale p X n),
    equivalence (completedEtaleGalois p X σ n a) =
      completedHodgeGalois p X σ n (equivalence a)

end MathlibExt.AlgebraicGeometry.HodgeTateComparison
