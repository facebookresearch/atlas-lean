/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.NodalTorsion

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

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

/-- The nodal cubic `y² = x³ + x²` over `ZMod 3`. -/
private def nodalCubic : WeierstrassCurve (ZMod 3) := ⟨0, 1, 0, 0, 0⟩

private theorem nodalCubic_equation : nodalCubic.toAffine.Equation 0 0 := by
  rw [Affine.equation_iff']; decide

private theorem nodalCubic_singular : ¬ nodalCubic.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']; decide

/-- The singular point `(0, 0)` of `nodalCubic` is a node: `b₂ = 4 = 1` in `ZMod 3`. -/
private theorem nodalCubic_isNode : nodalCubic.b₂ + 12 * 0 ≠ 0 := by
  decide

/-- The nonsingular point `(2, 0)` of `nodalCubic`. -/
private def nodalPoint : nodalCubic.toAffine.Point :=
  .some 2 0 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

private theorem two_nsmul_nodalPoint : 2 • nodalPoint = 0 := by
  decide

/-- A concrete instance: in characteristic `3` the theorem shows that the nonzero point `(2, 0)`
of `nodalCubic` is not `3`-torsion. -/
example : 3 • nodalPoint ≠ 0 := fun h =>
  Affine.Point.some_ne_zero _ <|
    Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode nodalCubic 0 0 nodalCubic_equation
      nodalCubic_singular nodalCubic_isNode nodalPoint h

/-- The characteristic hypothesis cannot be dropped: the nonzero point `(2, 0)` of `nodalCubic`
is `2`-torsion in characteristic `3`. -/
example : ¬ ∀ (k : Type) [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve k) (x₀ y₀ : k), W.toAffine.Equation x₀ y₀ →
      ¬ W.toAffine.Nonsingular x₀ y₀ → W.b₂ + 12 * x₀ ≠ 0 →
        ∀ P : W.toAffine.Point, p • P = 0 → P = 0 := fun h =>
  Affine.Point.some_ne_zero _ <| h (ZMod 3) (p := 2) nodalCubic 0 0 nodalCubic_equation
    nodalCubic_singular nodalCubic_isNode nodalPoint two_nsmul_nodalPoint

/-- The theorem does not apply with `p = 2` in characteristic `3`. -/
example : True := by
  fail_if_success
    have := Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode (k := ZMod 3) (p := 2)
  trivial

/-- The primality hypothesis rules out `p = 0` in characteristic `0`, where `0 • P = 0` holds for
every point. -/
example : True := by
  fail_if_success
    have := Affine.Point.eq_zero_of_prime_smul_eq_zero_of_isNode (k := ℚ) (p := 0)
  trivial

/-- The cuspidal cubic `y² = x³` over `ZMod 2`. -/
private def cuspidalCubic : WeierstrassCurve (ZMod 2) := ⟨0, 0, 0, 0, 0⟩

/-- The nonsingular point `(1, 1)` of `cuspidalCubic`. -/
private def cuspPoint : cuspidalCubic.toAffine.Point :=
  .some 1 1 (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide)

private theorem two_nsmul_cuspPoint : 2 • cuspPoint = 0 := by
  decide

/-- The node hypothesis cannot be dropped: at the cusp `(0, 0)` of `cuspidalCubic`, where
`b₂ + 12 * 0 = 0`, every other hypothesis holds, and `(1, 1)` is a nonzero `2`-torsion point. -/
example : ¬ ∀ (k : Type) [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) (x₀ y₀ : k), W.toAffine.Equation x₀ y₀ →
      ¬ W.toAffine.Nonsingular x₀ y₀ → ∀ P : W.toAffine.Point, p • P = 0 → P = 0 := fun h =>
  Affine.Point.some_ne_zero _ <| h (ZMod 2) (p := 2) cuspidalCubic 0 0
    (by rw [Affine.equation_iff']; decide)
    (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide) cuspPoint two_nsmul_cuspPoint
