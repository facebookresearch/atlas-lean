/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.HasseInvariant
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ

open WeierstrassCurve

example {R : Type*} [CommRing R] (t : R) : legendreCurve t = ⟨0, -(1 + t), 0, t, 0⟩ := rfl

example {F : Type*} [Field F] (q : ℕ) (W : WeierstrassCurve F) :
    W.hasseInvariant q = (W.twoTorsionPolynomial.toPoly ^ ((q - 1) / 2)).coeff (q - 1) := rfl

/-! The completed square: a polynomial identity over every ring, but a change of curve model only
when `2` is invertible. -/

-- `(2y + a₁x + a₃)² - Ψ(x)` is `4` times the Weierstrass polynomial, over any commutative ring.
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y : R) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 - W.twoTorsionPolynomial.toPoly.eval x =
      4 * W.toAffine.polynomial.evalEval x y := by
  rw [eval_toPoly_twoTorsionPolynomial, Affine.evalEval_polynomial]
  simp only [b₂, b₄, b₆]
  ring

private def charTwoCurve : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

-- Over `ZMod 2` the identity says nothing: for `y² + y = x³` it holds at `(1, 0)`, which is not a
-- point of the curve.
example : (2 * 0 + charTwoCurve.a₁ * 1 + charTwoCurve.a₃) ^ 2 =
      charTwoCurve.twoTorsionPolynomial.toPoly.eval 1 ∧
    ¬charTwoCurve.toAffine.Equation 1 0 := by
  refine ⟨?_, ?_⟩
  · rw [eval_toPoly_twoTorsionPolynomial]
    simp only [charTwoCurve, b₂, b₄, b₆]
    decide
  · rw [Affine.equation_iff]
    simp only [charTwoCurve]
    decide

/-! Small primes: the Hasse coefficient in closed form. -/

private theorem hasseInvariant_three {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.hasseInvariant 3 = W.b₂ := by
  rw [hasseInvariant, show (3 - 1) / 2 = 1 from rfl, show 3 - 1 = 2 from rfl, pow_one,
    Cubic.coeff_eq_b]
  rfl

private theorem hasseInvariant_five {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.hasseInvariant 5 = W.b₂ ^ 2 + 16 * W.b₄ := by
  rw [hasseInvariant, show (5 - 1) / 2 = 2 from rfl, show 5 - 1 = 4 from rfl, sq,
    Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Cubic.coeff_eq_a, Cubic.coeff_eq_b, Cubic.coeff_eq_c, Cubic.coeff_eq_d,
    Cubic.coeff_eq_zero, twoTorsionPolynomial]
  ring

private theorem hasseInvariant_seven {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.hasseInvariant 7 = W.b₂ ^ 3 + 48 * W.b₂ * W.b₄ + 48 * W.b₆ := by
  rw [hasseInvariant, show (7 - 1) / 2 = 3 from rfl, show 7 - 1 = 6 from rfl, pow_succ, sq]
  simp only [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Cubic.coeff_eq_a, Cubic.coeff_eq_b, Cubic.coeff_eq_c, Cubic.coeff_eq_d,
    Cubic.coeff_eq_zero, twoTorsionPolynomial]
  ring

-- At `q = 2` the exponent `(2 - 1) / 2` is `0`, so the coefficient vanishes for every curve; this
-- is why `ModularCurve.ssJSetHasse` requires characteristic different from two.
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.hasseInvariant 2 = 0 := by
  rw [hasseInvariant, show (2 - 1) / 2 = 0 from rfl, pow_zero, Polynomial.coeff_one]
  simp

private theorem hasseInvariant_five_of_charP {R : Type*} [CommRing R] [CharP R 5]
    (W : WeierstrassCurve R) : W.hasseInvariant 5 = W.c₄ := by
  rw [hasseInvariant_five, c₄]
  linear_combination (8 * W.b₄) * CharP.cast_eq_zero R 5

private theorem hasseInvariant_seven_of_charP {R : Type*} [CommRing R] [CharP R 7]
    (W : WeierstrassCurve R) : W.hasseInvariant 7 = -W.c₆ := by
  rw [hasseInvariant_seven, c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 24 * W.b₆) * CharP.cast_eq_zero R 7

private theorem j_eq_1728_iff {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    W.j = 1728 ↔ W.c₆ = 0 := by
  rw [W.j_eq, inv_mul_eq_iff_eq_mul₀ W.isUnit_Δ.ne_zero, ← pow_eq_zero_iff two_ne_zero]
  constructor <;> intro h
  · linear_combination h + W.c_relation
  · linear_combination h - W.c_relation

/-! The supersingular `j`-invariants in characteristics `3`, `5` and `7` are `0`, `0` and `1728`;
the Hasse description computes exactly these. -/

variable {K : Type*} [Field K] [Finite K] [NeZero (2 : K)]

private theorem ssJSetHasse_three [CharP K 3] : ModularCurve.ssJSetHasse 3 K = {0} := by
  classical
  ext j
  change (∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant 3 = 0) ↔ j = 0
  constructor
  · intro h
    have h0 := h (ofJ j) (ofJ_j j)
    rw [hasseInvariant_three] at h0
    rw [← ofJ_j j]
    exact (ofJ j).j_eq_zero_of_char_three h0
  · rintro rfl W _ hW
    rw [hasseInvariant_three]
    exact W.j_eq_zero_iff_of_char_three.mp hW

private theorem ssJSetHasse_five [CharP K 5] : ModularCurve.ssJSetHasse 5 K = {0} := by
  classical
  ext j
  change (∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant 5 = 0) ↔ j = 0
  constructor
  · intro h
    have h0 := h (ofJ j) (ofJ_j j)
    rw [hasseInvariant_five_of_charP] at h0
    rw [← ofJ_j j]
    exact (ofJ j).j_eq_zero h0
  · rintro rfl W _ hW
    rw [hasseInvariant_five_of_charP]
    exact W.j_eq_zero_iff.mp hW

private theorem ssJSetHasse_seven [CharP K 7] : ModularCurve.ssJSetHasse 7 K = {1728} := by
  classical
  ext j
  change (∀ (W : WeierstrassCurve K) [W.IsElliptic], W.j = j → W.hasseInvariant 7 = 0) ↔
    j = 1728
  constructor
  · intro h
    have h0 := h (ofJ j) (ofJ_j j)
    rw [hasseInvariant_seven_of_charP, neg_eq_zero] at h0
    rw [← ofJ_j j]
    exact (j_eq_1728_iff (ofJ j)).mpr h0
  · rintro rfl W _ hW
    rw [hasseInvariant_seven_of_charP, neg_eq_zero]
    exact (j_eq_1728_iff W).mp hW

-- A concrete field satisfying the hypotheses: in `ZMod 7`, `1728 = 6`.
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private instance : NeZero (2 : ZMod 7) := ⟨by decide⟩

example : ModularCurve.ssJSetHasse 7 (ZMod 7) = {6} := by
  rw [ssJSetHasse_seven]
  congr 1
