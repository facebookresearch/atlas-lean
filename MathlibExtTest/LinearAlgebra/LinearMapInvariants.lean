/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.LinearMapInvariants

@[expose] public section

example {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2)
    (f : M →ₗ[R] M) :
    f.charpoly = Polynomial.X ^ 2 - Polynomial.C (LinearMap.trace R M f)
      * Polynomial.X + Polynomial.C (LinearMap.det f) :=
  LinearMap.charpoly_of_finrank_eq_two h f

example {R : Type*} {M : Type*} {N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (f : Module.End R M) (g : Module.End R N) (h : ∀ x : M, e (f x) = g (e x)) :
    LinearMap.trace R M f = LinearMap.trace R N g ∧ LinearMap.det f = LinearMap.det g :=
  LinearMap.trace_eq_and_det_eq_of_semiconj e f g h

example {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) :
    Module.finrank K (LinearMap.ker f.dualMap) = Module.finrank K (LinearMap.ker f) :=
  LinearMap.finrank_ker_dualMap_eq_finrank_ker f
