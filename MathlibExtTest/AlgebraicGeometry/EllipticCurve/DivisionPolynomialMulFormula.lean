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

/-- The curve `y ^ 2 = x ^ 3 + 1` over `ℚ`, with the points `P = (2, 3)` and
`Q = (0, 1)`. Here `x (P + Q) = -1`, `x (P - Q) = 2` and `x (2 • P) = 0`. -/
private abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 1 }

private theorem equation_P : E.toAffine.Equation 2 3 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num

private theorem equation_Q : E.toAffine.Equation 0 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num

/-- The sum identity at `P` and `Q`: `(x (P + Q) + x (P - Q)) * (2 - 0) ^ 2`
is `(-1 + 2) * 4 = 4`. -/
example :
    (E.toAffine.addX 2 0 (E.toAffine.slope 2 0 3 1) +
        E.toAffine.addX 2 0 (E.toAffine.slope 2 0 3 (E.toAffine.negY 0 1))) *
        (2 - 0) ^ 2 = 4 :=
  (WeierstrassCurve.Affine.addX_add_addX_negY_mul_sq equation_P equation_Q
    (by norm_num)).trans (by norm_num [b₂, b₄, b₆])

/-- The product identity at `P` and `Q`: `x (P + Q) * x (P - Q) * (2 - 0) ^ 2`
is `-1 * 2 * 4 = -8`. -/
example :
    E.toAffine.addX 2 0 (E.toAffine.slope 2 0 3 1) *
        E.toAffine.addX 2 0 (E.toAffine.slope 2 0 3 (E.toAffine.negY 0 1)) *
        (2 - 0) ^ 2 = -8 :=
  (WeierstrassCurve.Affine.addX_mul_addX_negY_mul_sq equation_P equation_Q
    (by norm_num)).trans (by norm_num [b₄, b₆, b₈])

/-- The doubling identity at `P`: `x (2 • P) * (Ψ₂Sq).eval 2 = (Φ 2).eval 2 = 0`. -/
example :
    E.toAffine.addX 2 2 (E.toAffine.slope 2 2 3 3) * (E.Ψ₂Sq).eval 2 = 0 :=
  (WeierstrassCurve.Affine.addX_self_mul_Ψ₂Sq equation_P
    (by norm_num [WeierstrassCurve.Affine.negY])).trans
    (by rw [WeierstrassCurve.Affine.eval_Φ_two]; norm_num [b₄, b₆, b₈])

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.DivisionPolynomialMulFormula
