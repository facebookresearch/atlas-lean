/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula

open WeierstrassCurve Polynomial

universe u

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/-- Unfolding consumer: `MFred` at `1` with its definition expanded. -/
example {x y : F} (h : W.toAffine.Nonsingular x y) :
    WeierstrassCurve.Affine.MFred 1 h ↔
      (W.ΨSq (1 : ℤ)).eval x ≠ 0 ∧
        (1 • (WeierstrassCurve.Affine.Point.some x y h :
          W.toAffine.Point)).xCoordOrZero * (W.ΨSq (1 : ℤ)).eval x =
          (W.Φ (1 : ℤ)).eval x :=
  Iff.rfl

/-- Characterization consumer: `MFred 1` holds for every nonsingular
point, and `MFred 2` holds whenever doubling the point is nonzero.
Both instantiate all hypotheses of the corresponding lemmas. -/
example {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 • (WeierstrassCurve.Affine.Point.some x y h :
      W.toAffine.Point)) ≠ 0) :
    WeierstrassCurve.Affine.MFred 1 h ∧
      WeierstrassCurve.Affine.MFred 2 h :=
  ⟨WeierstrassCurve.Affine.mfred_one h,
    WeierstrassCurve.Affine.mfred_two h h2⟩

/-- Low-torsion-freeness is monotone in the bound. -/
example {x y : F} {h : W.toAffine.Nonsingular x y} {m n : ℕ}
    (hmn : m ≤ n) (hf : WeierstrassCurve.Affine.LowTorsionFree n h) :
    WeierstrassCurve.Affine.LowTorsionFree m h :=
  hf.mono hmn

/-- The star identity unfolds to its defining equation in `R[X]`. -/
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j : ℤ) :
    W.StarIdentity j ↔
      2 * X * W.Φ j * (W.Φ j + X * W.ΨSq j) + C W.b₂ * X * (W.Φ j * W.ΨSq j) +
          C W.b₄ * ((W.Φ j + X * W.ΨSq j) * W.ΨSq j) + C W.b₆ * W.ΨSq j ^ 2 =
        W.Φ (j + 1) * W.ΨSq (j - 1) + W.Φ (j - 1) * W.ΨSq (j + 1) :=
  Iff.rfl

/-- Evaluation consumer: the star identity gives the corresponding
equation between the values at every `t : R`. -/
example {R : Type u} [CommRing R] {W : WeierstrassCurve R} {j : ℤ}
    (h : W.StarIdentity j) (t : R) :
    2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
        W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
        W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) *
          (W.ΨSq j).eval t) +
        W.b₆ * (W.ΨSq j).eval t ^ 2 =
      (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
        (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t :=
  h.eval t

/-- The star identity holds at `j = 1` over every commutative ring. -/
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W.StarIdentity 1 := by
  change _ = _
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, Φ_one,
    ΨSq_one, Φ_zero, ΨSq_zero, ΨSq_two, Ψ₂Sq]
  simp only [map_ofNat, C_mul]
  ring

/-- The star identity also holds at `j = 2` over every commutative ring. -/
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W.StarIdentity 2 := by
  change _ = _
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, Φ_one,
    ΨSq_one, Φ_two, ΨSq_two, Φ_three, ΨSq_three, Ψ₂Sq, Ψ₃, preΨ₄]
  simp only [b₂, b₄, b₆, b₈, map_ofNat, C_add, C_sub, C_mul, C_pow]
  ring

/-- An addition-formula instance: the secant-slope identity for two
points with distinct `x`-coordinates, with all hypotheses supplied. -/
example {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 :=
  WeierstrassCurve.Affine.addX_mul_sq_of_X_ne y₁ y₂ hx

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
