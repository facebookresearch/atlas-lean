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
theorem exactSource {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
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
