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
# Canonical free coordinates after scalar extension

The native scalar extension of the standard finitely supported basis has
the same original index. Its representation gives an acting-algebra-linear
equivalence `R ⊗_k (I →₀ k) ≃ I →₀ R`, with independent universes and no
finite index or chosen ordering. The standard basis is used directly.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w

namespace Finsupp

variable (k : Type u) [CommRing k] (R : Type v) [CommRing R] [Algebra k R]
  (I : Type w)

/-- Original standard free coordinates commute with scalar extension. -/
def scalarExtensionCoordinates : R ⊗[k] (I →₀ k) ≃ₗ[R] (I →₀ R) :=
  ((Finsupp.basisSingleOne (R := k) (ι := I)).baseChange R).repr

/-- Every original coordinate is extended by the original algebra map. -/
theorem scalarExtensionCoordinates_tmul_apply (r : R) (v : I →₀ k) (i : I) :
    scalarExtensionCoordinates k R I (r ⊗ₜ[k] v) i = algebraMap k R (v i) * r := by
  rw [scalarExtensionCoordinates, Module.Basis.baseChange_repr_tmul]
  change (v i) • r = algebraMap k R (v i) * r
  exact Algebra.smul_def _ _

/-- A standard pure coordinate keeps its original index and extended coefficient. -/
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

/-- The inverse standard coordinate inserts the actual scalar unit in its original free generator. -/
theorem scalarExtensionCoordinates_symm_single (i : I) (r : R) :
    (scalarExtensionCoordinates k R I).symm (single i r) =
      r ⊗ₜ[k] single i (1 : k) := by
  apply (scalarExtensionCoordinates k R I).injective
  rw [LinearEquiv.apply_symm_apply, scalarExtensionCoordinates_tmul_single,
    map_one, one_mul]

/-- The original scalar-extension coordinate sends the original extended standard basis
element to its actual standard coordinate. -/
theorem scalarExtensionCoordinates_basis (i : I) :
    scalarExtensionCoordinates k R I
      ((1 : R) ⊗ₜ[k] single i (1 : k)) = single i (1 : R) := by
  rw [scalarExtensionCoordinates_tmul_single, map_one, one_mul]

end Finsupp
