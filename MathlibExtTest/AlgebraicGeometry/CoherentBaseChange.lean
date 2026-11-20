/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CoherentBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open CoherentBaseChange TwoChartCech
open scoped TensorProduct

universe u v w

-- Consumer with the original binders: the base-change comparison map
-- for a two-term complex of finite free modules.
example {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)
    (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker G.d)) :
    (G.kerBaseChangeHom A x : A ⊗[R] G.C0) =
      (LinearMap.ker G.d).subtype.baseChange A x :=
  G.kerBaseChangeHom_apply_coe A x

-- The fibre invariants and Euler characteristic of a two-term complex.
example {R : Type u} [CommRing R] (G : TwoTermComplex.{u, v} R)
    (𝔭 : PrimeSpectrum R) :
    G.fibreH0 𝔭 = G.fibreH0 𝔭 ∧ G.fibreH1 𝔭 = G.fibreH1 𝔭 ∧
      G.chi = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ) :=
  ⟨rfl, rfl, rfl⟩

-- Higher-universe consumer for Mumford's truncation.
example {R : Type u} [CommRing R] {C0 : Type v} {C1 : Type w}
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (z : C0 × (Fin (Mumford.rank d) → R)) :
    (z ∈ Mumford.K0 d ↔ d z.1 + Mumford.lift d z.2 = 0) :=
  Mumford.mem_K0_iff d z

-- Mumford's square commutes, with the original `Type` binder.
example (R : Type) [CommRing R] :
    (0 : R →ₗ[R] R) ∘ₗ Mumford.ι0 (0 : R →ₗ[R] R) =
      Mumford.ι1 (0 : R →ₗ[R] R) ∘ₗ Mumford.dK (0 : R →ₗ[R] R) :=
  Mumford.comm 0

-- The two-chart kernel at the zero map: membership is a condition only
-- on the lift.
example (x : ℤ) (v : Fin (Mumford.rank (0 : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (x, v) ∈ Mumford.K0 (0 : ℤ →ₗ[ℤ] ℤ) ↔
      Mumford.lift (0 : ℤ →ₗ[ℤ] ℤ) v = 0 := by
  rw [Mumford.mem_K0_iff, LinearMap.zero_apply, zero_add]

example (v : Fin (Mumford.rank (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) → ℤ) :
    (-(Mumford.lift (LinearMap.id : ℤ →ₗ[ℤ] ℤ) v), v) ∈
      Mumford.K0 (LinearMap.id : ℤ →ₗ[ℤ] ℤ) := by
  rw [Mumford.mem_K0_iff, LinearMap.id_apply, neg_add_cancel]

-- The generic two-chart kernel with a zero second map.
example {R : Type u} [CommRing R] (d : R →ₗ[R] R) (x : R) (p : PUnit) :
    (x, p) ∈ KerCoprod.K0 d (0 : PUnit →ₗ[R] R) ↔ d x = 0 := by
  rw [KerCoprod.mem_K0_iff, LinearMap.zero_apply, add_zero]

-- Surjectivity of the coproduct built from Mumford's lift.
example {R : Type u} [CommRing R] {C0 : Type v} {C1 : Type w}
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Function.Surjective (d.coprod (Mumford.lift d)) :=
  Mumford.surjective_coprod d

-- A fibre family over a scheme records the local fibre dimensions.
example {T : Scheme.{u}} (F : FibreH0Family.{u} T) (U : T.Opens)
    (hU : IsAffineOpen U) (t : U) :
    F.h0 t = (F.G U hU).fibreH0 (hU.primeIdealOf t) :=
  F.hglue U hU t
