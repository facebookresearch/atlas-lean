/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

/-- The star identity unfolds to its defining polynomial equation. -/
example {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j : ℤ) :
    W.StarIdentity j ↔
      ∀ t : R,
        2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
            W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
            W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) *
              (W.ΨSq j).eval t) +
            W.b₆ * (W.ΨSq j).eval t ^ 2 =
          (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
            (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t :=
  Iff.rfl

/-- An addition-formula instance: the secant-slope identity for two
points with distinct `x`-coordinates, with all hypotheses supplied. -/
example {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 :=
  WeierstrassCurve.Affine.addX_mul_sq_of_X_ne y₁ y₂ hx

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
