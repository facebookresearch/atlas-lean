/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_AddFormula.lean`,
`Definitions/Def_WeierstrassCurve_DivPolyMulFormula.lean`
and
`Definitions/Def_WeierstrassCurve_DivPolyMulFormulaCore.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Multiplication formula predicates for division polynomials

This file defines the predicates used to state the multiplication formula
for the division polynomials of a Weierstrass curve, together with the
affine addition-formula identities from which the formula is derived.

For a nonsingular affine point `P = (x, y)`, `MFred W m h` says that the
`x`-coordinate of `m • P` is `Φ m` evaluated at `x`, divided by `ΨSq m`
evaluated at `x`, expressed without division as
`xCoordOrZero (m • P) * (ΨSq m).eval x = (Φ m).eval x`, together with
`(ΨSq m).eval x ≠ 0`. `LowTorsionFree W m h` says that no multiple
`k • P` with `1 ≤ k ≤ m` vanishes. `StarIdentity W j` is the polynomial
identity in one variable that drives the induction step.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The star identity for the division polynomials of `W` at index `j`:
the polynomial identity in `t` relating `Φ` and `ΨSq` at `j - 1`, `j`,
and `j + 1` that drives the induction step of the multiplication
formula. -/
def StarIdentity (j : ℤ) : Prop :=
  ∀ t : R,
    2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
        W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
        W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) * (W.ΨSq j).eval t) +
        W.b₆ * (W.ΨSq j).eval t ^ 2 =
      (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
        (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t

namespace Affine

variable {F : Type v} [Field F] {W : WeierstrassCurve F}

/-- The `x`-coordinate of an affine point, or `0` for the point at
infinity. -/
def Point.xCoordOrZero (P : W.toAffine.Point) : F :=
  match P with
  | .zero => 0
  | .some x _ _ => x

@[simp]
lemma Point.xCoordOrZero_zero : (0 : W.toAffine.Point).xCoordOrZero = 0 :=
  rfl

@[simp]
lemma Point.xCoordOrZero_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (Point.some x y h).xCoordOrZero = x :=
  rfl

/-- The multiplication-formula predicate at index `m` for the point
`(x, y)`: `(ΨSq m).eval x` is nonzero and the `x`-coordinate of
`m • (x, y)` times `(ΨSq m).eval x` equals `(Φ m).eval x`. -/
def MFred [DecidableEq F] (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
    (m • (Point.some x y h : W.toAffine.Point)).xCoordOrZero *
        (W.ΨSq (m : ℤ)).eval x =
      (W.Φ (m : ℤ)).eval x

/-- No multiple `k • (x, y)` with `1 ≤ k ≤ m` is the point at
infinity. -/
def LowTorsionFree [DecidableEq F] (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) :
    Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ m → k • (Point.some x y h : W.toAffine.Point) ≠ 0

lemma LowTorsionFree.mono [DecidableEq F] {m n : ℕ} (hmn : m ≤ n) {x y : F}
    {h : W.toAffine.Nonsingular x y} (hf : LowTorsionFree n h) :
    LowTorsionFree m h :=
  fun k hk1 hkm => hf k hk1 (hkm.trans hmn)

section EvalLemmas

lemma eval_Ψ₂Sq (x : F) :
    (W.Ψ₂Sq).eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [Ψ₂Sq]

lemma eval_Φ_two (x : F) :
    (W.Φ 2).eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  simp [Φ_two]

lemma sq_sub_negY_eq_eval_Ψ₂Sq {x y : F} (h : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = (W.Ψ₂Sq).eval x := by
  rw [Affine.equation_iff] at h
  rw [eval_Ψ₂Sq, Affine.negY, b₂, b₄, b₆]
  linear_combination 4 * h

lemma Ψ₂Sq_eval_ne_zero {x y : F} (h : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) : (W.Ψ₂Sq).eval x ≠ 0 := by
  rw [← sq_sub_negY_eq_eval_Ψ₂Sq h]
  exact pow_ne_zero 2 (sub_ne_zero.mpr hy)

lemma Ψ₂Sq_eval_eq_zero_iff_two_smul [DecidableEq F] {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (W.Ψ₂Sq).eval x = 0 ↔
      (2 • Point.some x y h : W.toAffine.Point) = 0 := by
  rw [two_nsmul]
  constructor
  · intro h0
    have hy : y = W.toAffine.negY x y := by
      by_contra hy
      exact Ψ₂Sq_eval_ne_zero h.left hy h0
    exact Point.add_self_of_Y_eq hy
  · intro h0
    by_cases hy : y = W.toAffine.negY x y
    · rw [← sq_sub_negY_eq_eval_Ψ₂Sq h.left, sub_eq_zero.mpr hy]
      ring
    · exact absurd ((Point.add_self_of_Y_ne hy).symm.trans h0)
        (Point.some_ne_zero _)

end EvalLemmas

section Slope

variable [DecidableEq F]

lemma addX_mul_sq_of_X_ne {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) ^ 2 =
      (y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.slope_of_X_ne hx, Affine.addX]
  field_simp
  ring

theorem addX_add_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
        W.toAffine.addX x₁ x₂
          (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
        (x₁ - x₂) ^ 2 =
      2 * (x₁ * x₂) * (x₁ + x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) +
        W.b₆ := by
  have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
  have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.toAffine.negY x₂ y₂) hx
  rw [Affine.equation_iff] at h₁ h₂
  rw [add_mul, e₁, e₂, Affine.negY, b₂, b₄, b₆]
  linear_combination 2 * h₁ + 2 * h₂

theorem addX_mul_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
        W.toAffine.addX x₁ x₂
          (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
        (x₁ - x₂) ^ 2 =
      (x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈ := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have e₁ := addX_mul_sq_of_X_ne (W := W) y₁ y₂ hx
  have e₂ := addX_mul_sq_of_X_ne (W := W) y₁ (W.toAffine.negY x₂ y₂) hx
  have key : ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
      ((y₁ - W.toAffine.negY x₂ y₂) ^ 2 +
        W.a₁ * (y₁ - W.toAffine.negY x₂ y₂) * (x₁ - x₂) -
        (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) =
      ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) *
        (x₁ - x₂) ^ 2 := by
    rw [Affine.equation_iff] at h₁ h₂
    rw [Affine.negY, b₄, b₆, b₈]
    linear_combination
      (W.a₁ ^ 2 * x₁ * x₂ - W.a₁ ^ 2 * x₂ ^ 2 + W.a₁ * W.a₃ * x₁ -
          W.a₁ * W.a₃ * x₂ + W.a₁ * x₁ * y₁ - 2 * W.a₁ * x₂ * y₂ -
          W.a₂ * x₁ ^ 2 + 4 * W.a₂ * x₁ * x₂ - 2 * W.a₂ * x₂ ^ 2 +
          W.a₃ * y₁ - 2 * W.a₃ * y₂ + W.a₄ * x₁ + W.a₆ - x₁ ^ 3 +
          2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - 2 * x₂ ^ 3 + y₁ ^ 2 -
          2 * y₂ ^ 2) * h₁ +
      (-W.a₁ ^ 2 * x₁ ^ 2 + W.a₁ ^ 2 * x₁ * x₂ - W.a₁ * W.a₃ * x₁ +
          W.a₁ * W.a₃ * x₂ + W.a₁ * x₂ * y₂ - 4 * W.a₂ * x₁ ^ 2 +
          4 * W.a₂ * x₁ * x₂ - W.a₂ * x₂ ^ 2 + W.a₃ * y₂ -
          2 * W.a₄ * x₁ + W.a₄ * x₂ - W.a₆ - 4 * x₁ ^ 3 +
          2 * x₁ ^ 2 * x₂ + 2 * x₁ * x₂ ^ 2 - x₂ ^ 3 + y₂ ^ 2) * h₂
  apply mul_left_cancel₀ hd2
  calc (x₁ - x₂) ^ 2 *
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
          W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
          (x₁ - x₂) ^ 2)
      = (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) *
            (x₁ - x₂) ^ 2) *
          (W.toAffine.addX x₁ x₂
            (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)) *
            (x₁ - x₂) ^ 2) := by ring
    _ = ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
            (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) *
          ((y₁ - W.toAffine.negY x₂ y₂) ^ 2 +
            W.a₁ * (y₁ - W.toAffine.negY x₂ y₂) * (x₁ - x₂) -
            (W.a₂ + x₁ + x₂) * (x₁ - x₂) ^ 2) := by rw [e₁, e₂]
    _ = ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) - W.b₈) *
          (x₁ - x₂) ^ 2 := key
    _ = (x₁ - x₂) ^ 2 *
          ((x₁ * x₂) ^ 2 - W.b₄ * (x₁ * x₂) - W.b₆ * (x₁ + x₂) -
            W.b₈) := by ring

lemma addX_self_mul_sq_of_Y_ne {x₁ y₁ : F}
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) *
        (y₁ - W.toAffine.negY x₁ y₁) ^ 2 =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) ^ 2 +
        W.a₁ * (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) *
          (y₁ - W.toAffine.negY x₁ y₁) -
        (W.a₂ + x₁ + x₁) * (y₁ - W.toAffine.negY x₁ y₁) ^ 2 := by
  have hψ : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
  rw [Affine.slope_of_Y_ne rfl hy, Affine.addX]
  field_simp
  ring

theorem addX_self_mul_Ψ₂Sq {x₁ y₁ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) *
        (W.Ψ₂Sq).eval x₁ =
      (W.Φ 2).eval x₁ := by
  rw [← sq_sub_negY_eq_eval_Ψ₂Sq h₁, addX_self_mul_sq_of_Y_ne hy,
    eval_Φ_two]
  rw [Affine.equation_iff] at h₁
  rw [Affine.negY, b₄, b₆, b₈]
  linear_combination (-W.a₁ ^ 2 - 4 * W.a₂ - 8 * x₁) * h₁

theorem addX_self_mul_ΨSq_two {x₁ y₁ : F}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) *
        (W.ΨSq 2).eval x₁ =
      (W.Φ 2).eval x₁ := by
  rw [ΨSq_two]
  exact addX_self_mul_Ψ₂Sq h₁ hy

end Slope

section BaseCases

theorem mfred_one [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y) :
    MFred 1 h := by
  constructor
  · rw [Nat.cast_one, ΨSq_one]
    simp
  · rw [Nat.cast_one, ΨSq_one, Φ_one, one_nsmul, Point.xCoordOrZero_some]
    simp

theorem mfred_two [DecidableEq F] {x y : F} (h : W.toAffine.Nonsingular x y)
    (h2 : (2 • (Point.some x y h : W.toAffine.Point)) ≠ 0) : MFred 2 h := by
  have hy : y ≠ W.toAffine.negY x y := fun hy =>
    h2 (by rw [two_nsmul]; exact Point.add_self_of_Y_eq hy)
  have hcast : ((2 : ℕ) : ℤ) = 2 := by norm_num
  have hΨ2 : (W.Ψ₂Sq).eval x ≠ 0 := Ψ₂Sq_eval_ne_zero h.left hy
  constructor
  · rw [hcast, ΨSq_two]
    exact hΨ2
  · have hns2 : W.toAffine.Nonsingular
        (W.toAffine.addX x x (W.toAffine.slope x x y y))
        (W.toAffine.addY x x y (W.toAffine.slope x x y y)) :=
      Affine.nonsingular_add h h fun hxy => hy hxy.right
    have h2P : (2 • (Point.some x y h : W.toAffine.Point)) =
        Point.some _ _ hns2 := by
      rw [two_nsmul]
      exact Point.add_self_of_Y_ne hy
    rw [hcast, ΨSq_two, h2P, Point.xCoordOrZero_some]
    exact addX_self_mul_Ψ₂Sq h.left hy

end BaseCases

end Affine

end WeierstrassCurve
