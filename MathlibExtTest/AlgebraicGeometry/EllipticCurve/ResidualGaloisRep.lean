/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ResidualGaloisRep

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

/-- Importing the module adds no `DecidableEq` instance on `AlgebraicClosure ℚ`: the classical
instance the point API needs is local to the module, and importers choose their own (below,
with `open Classical in`). -/
example : True := by
  fail_if_success
    have : DecidableEq (AlgebraicClosure ℚ) := inferInstance
  trivial

-- Source consumer with the original binders.
open Classical in
example (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p))
    (q : ℕ) :
    (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q ↔
      WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt
        (S := ℚ) (K := AlgebraicClosure ℚ) W p q :=
  WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff W p hcard hker q

-- Unfolding consumer: under the torsion-count and finite-level hypotheses that construct it,
-- unramifiedness of the attached representation means inertia acts trivially on every
-- `p`-torsion point.
open Classical in
example (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p))
    (q : ℕ)
    (h : (W.residualGaloisRepOf p hcard hker).IsUnramifiedAt q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :
    σ • x = x := by
  have h1 := (WeierstrassCurve.residualGaloisRepOf_isUnramifiedAt_iff
    W p hcard hker q).1 h A hA σ hσ x
  exact h1

-- The attached representation is two-dimensional over `ZMod p`.
open Classical in
example (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card
      (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (S := ℚ) (K := AlgebraicClosure ℚ) W p)) :
    Module.finrank (ZMod p) (W.residualGaloisRepOf p hcard hker).V = 2 :=
  (W.residualGaloisRepOf p hcard hker).finrank_eq
