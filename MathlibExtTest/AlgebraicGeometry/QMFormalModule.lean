/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMFormalModule

/-!
# Tests for special formal modules and QM formal completion
-/

@[expose] public section

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped Quaternion

universe u

/-- A formal module over a fake elliptic curve unpacks to formal
coordinates. -/
private theorem exactSource {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (h : E.IsFormalModuleOf coord X) :
    ∃ θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2,
      E.IsFormalModuleVia coord X θ :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleOf_iff E coord X).mp h

/-- The identity series is a law homomorphism for every formal group. -/
example {B : Type u} [CommRing B] (F : MvFormalGroup 2 B) :
    IsLawHom F F (Series.id B) :=
  IsLawHom.id F

/-- Kernel degree of the action of `p` is the height predicate. -/
example {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
    (X : FormalODModule p B) (h : ℕ) :
    X.HasHeight h ↔ FormalODModule.HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h) :=
  Iff.rfl

open CategoryTheory AlgebraicGeometry in
/-- Formal coordinates are injective on points infinitesimal along a
square-zero ideal, so the constant family at the identity point is not a
system of formal coordinates over a nontrivial ring. -/
example {B : Type} [CommRing B] [Nontrivial B] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 1 B) :
    ¬ L.IsFormalCoordinates F (fun _ _ _ _ => L.one _) := by
  rintro ⟨-, h⟩
  have hJ : Ideal.span {(DualNumber.eps : DualNumber B)} ^ (1 + 1) = ⊥ := by
    rw [Ideal.span_singleton_pow, pow_two, DualNumber.eps_mul_eps,
      Ideal.span_singleton_eq_bot]
  have hst := (h (DualNumber B) _ 1 hJ).2.1 0 (fun _ => DualNumber.eps)
    (fun _ => Ideal.zero_mem _) (fun _ => Ideal.mem_span_singleton_self _) rfl
  simpa using congrArg (fun s => TrivSqZeroExt.snd (s 0)) hst
