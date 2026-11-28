/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Canonical free coordinates after scalar extension. -/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Free coordinates under scalar extension

For commutative rings k and R with R a k-algebra, scalar extension identifies R ⊗[k] (I →₀ k)
with the free R-module I →₀ R for any index type I. The R-linear equivalence sends a pure
tensor r ⊗ v to the function whose i-th value is algebraMap k R (v i) * r.

Its inverse sends single i r to r ⊗ single i 1. In particular, the extended unit-coordinate
basis maps to the unit-coordinate basis over R. The rings and index type may have different
carrier universes.

See Bourbaki, *Algebra*, Chapter III, for extension of scalars.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w

namespace Finsupp

variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
  (I : Type w)

/-- Let k and R be commutative rings with R a k-algebra, and let I be any index type. There is an
R-linear equivalence scalarExtensionCoordinates k R I : R ⊗[k] (I →₀ k) ≃ₗ[R] (I →₀ R). It
sends r ⊗ v to the finitely supported function i ↦ algebraMap k R (v i) * r. -/
def scalarExtensionCoordinates : R ⊗[k] (I →₀ k) ≃ₗ[R] (I →₀ R) := by
  classical
  exact TensorProduct.finsuppScalarRight k R R I

/-- Let k and R be commutative rings with R a k-algebra, and let I be any index type. For r : R, v
: I →₀ k and i : I, scalarExtensionCoordinates k R I (r ⊗ₜ[k] v) i = algebraMap k R (v i) * r. -/
theorem scalarExtensionCoordinates_tmul_apply (r : R) (v : I →₀ k) (i : I) :
    scalarExtensionCoordinates k R I (r ⊗ₜ[k] v) i = algebraMap k R (v i) * r := by
  classical
  change TensorProduct.finsuppScalarRight k R R I (r ⊗ₜ[k] v) i = _
  rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  exact Algebra.smul_def _ _

/-- Let k and R be commutative rings with R a k-algebra, and let I be any index type. For r : R, i
: I and c : k, scalarExtensionCoordinates k R I (r ⊗ₜ[k] single i c) = single i (algebraMap k
R c * r). -/
theorem scalarExtensionCoordinates_tmul_single (r : R) (i : I) (c : k) :
    scalarExtensionCoordinates k R I (r ⊗ₜ[k] single i c) =
      single i (algebraMap k R c * r) := by
  classical
  ext j
  rw [scalarExtensionCoordinates_tmul_apply]
  by_cases h : i = j
  · subst j
    simp only [single_eq_same]
  · have hji : j ≠ i := Ne.symm h
    rw [Finsupp.single_eq_of_ne hji, Finsupp.single_eq_of_ne hji, map_zero, zero_mul]

/-- Let k and R be commutative rings with R a k-algebra, and let I be any index type. For i : I
and r : R, the inverse equivalence sends single i r to r ⊗ₜ[k] single i (1 : k). -/
theorem scalarExtensionCoordinates_symm_single (i : I) (r : R) :
    (scalarExtensionCoordinates k R I).symm (single i r) =
      r ⊗ₜ[k] single i (1 : k) := by
  classical
  change (TensorProduct.finsuppScalarRight k R R I).symm (single i r) = _
  exact TensorProduct.finsuppScalarRight_symm_apply_single (R := k) (S := R) (M := R) i r

/-- Let k and R be commutative rings with R a k-algebra, and let I be any index type. For every i
: I, scalarExtensionCoordinates k R I ((1 : R) ⊗ₜ[k] single i (1 : k)) = single i (1 : R). -/
theorem scalarExtensionCoordinates_basis (i : I) :
    scalarExtensionCoordinates k R I
      ((1 : R) ⊗ₜ[k] single i (1 : k)) = single i (1 : R) := by
  rw [scalarExtensionCoordinates_tmul_single, map_one, one_mul]

end Finsupp
