/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.NodalTorsion

@[expose] public section

open WeierstrassCurve

example {k : Type*} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0)
    (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 :=
  WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode W x₀ y₀ he hs hnode P hP

example {k : Type 1} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0)
    (P : W.toAffine.Point) (hP : p • P = 0) : P = 0 :=
  WeierstrassCurve.Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode W x₀ y₀ he hs hnode P hP
