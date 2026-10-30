/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LinearMap_charpoly_of_finrank_eq_two.lean`,
`P2M/Sol/S_LinearMap_charpoly_of_finrank_eq_two.lean`,
`Theorems/Thm_LinearMap_trace_eq_and_det_eq_of_semiconj.lean`,
`P2M/Sol/S_LinearMap_trace_eq_and_det_eq_of_semiconj.lean`,
`Theorems/Thm_LinearMap_finrank_ker_dualMap_eq_finrank_ker.lean` and
`P2M/Sol/S_LinearMap_finrank_ker_dualMap_eq_finrank_ker.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Invariants of linear endomorphisms

Trace, determinant, and characteristic polynomial under conjugacy, and the
dimension of the kernel of the dual map.
-/

@[expose] public section

/-- The characteristic polynomial of an endomorphism of a free rank-two
module is `X² - tr f · X + det f`, the familiar quadratic formula. -/
theorem LinearMap.charpoly_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R]
    [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (h : Module.finrank R M = 2) (f : M →ₗ[R] M) :
    f.charpoly = Polynomial.X ^ 2 - Polynomial.C (LinearMap.trace R M f)
      * Polynomial.X + Polynomial.C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq R M h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace R b f, LinearMap.det_toMatrix b f]

/-- Trace and determinant are preserved under semiconjugacy: if `e` intertwines
`f` and `g`, then `g` is the conjugate of `f` by `e`, so both invariants agree. -/
theorem LinearMap.trace_eq_and_det_eq_of_semiconj {R : Type*} {M : Type*} {N : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (h : ∀ x : M, e (f x) = g (e x)) :
    LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g := by
  have hg : g = e.conj f := by
    ext y
    rw [LinearEquiv.conj_apply]
    simp [h]
  subst hg
  exact ⟨(LinearMap.trace_conj' f e).symm, (LinearMap.det_conj f e).symm⟩

/-- The kernel of the dual map has the same finite dimension as the kernel:
both are complementary to the range, by rank-nullity and the
dual-annihilator dimension formula. -/
theorem LinearMap.finrank_ker_dualMap_eq_finrank_ker {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker f.dualMap) = Module.finrank K (LinearMap.ker f) := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  omega
