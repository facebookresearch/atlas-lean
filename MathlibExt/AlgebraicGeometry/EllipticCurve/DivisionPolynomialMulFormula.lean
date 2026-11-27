/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_WeierstrassCurve_AddFormula.lean`,
`Definitions/Def_WeierstrassCurve_DivPolyMulFormula.lean`,
`Definitions/Def_WeierstrassCurve_DivPolyMulFormulaCore.lean`
and
`Definitions/Def_NetPairing_Basic.lean` (`Point.xOrZero` and its two lemmas, here
`Point.xCoordOrZero`, `Point.xCoordOrZero_zero` and `Point.xCoordOrZero_some`)
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
import Mathlib.Tactic.LinearCombination

/-!
# Multiplication formula predicates for division polynomials

This file defines the predicates used to state the multiplication formula
for the division polynomials of a Weierstrass curve, together with the
affine addition-formula identities from which the formula is derived.

For a nonsingular affine point `P = (x, y)` of a Weierstrass curve `W` over a
field, `MFred W m h` says that the
`x`-coordinate of `m • P` is `Φ m` evaluated at `x`, divided by `ΨSq m`
evaluated at `x`, expressed without division as
`xCoordOrZero (m • P) * (ΨSq m).eval x = (Φ m).eval x`, together with
`(ΨSq m).eval x ≠ 0`; `xCoordOrZero` is `0` at the point at infinity.
`LowTorsionFree W m h` says that no multiple
`k • P` with `1 ≤ k ≤ m` vanishes. `StarIdentity W j` is the equation
in `R[X]` that drives the induction step, and `StarIdentity.eval`
evaluates it at a point of `R`.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

universe u v

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **Star identity.** Let $W$ be a Weierstrass curve over a commutative ring $R$, and for
$i \in \mathbb{Z}$ let $\Phi_i$ and $\Psi_i^2$ be the polynomials `W.Φ i` and `W.ΨSq i` in $R[X]$.
The star identity at $j \in \mathbb{Z}$ is the equation in $R[X]$

$$2X\Phi_j\left(\Phi_j + X\Psi_j^2\right) + b_2X\Phi_j\Psi_j^2
+ b_4\left(\Phi_j + X\Psi_j^2\right)\Psi_j^2 + b_6\left(\Psi_j^2\right)^2
= \Phi_{j+1}\Psi_{j-1}^2 + \Phi_{j-1}\Psi_{j+1}^2,$$

where $b_2, b_4, b_6$ are the coefficients of $W$, read as constant polynomials. It drives the
induction step of the multiplication formula. As an equality of polynomials it is stronger than the
source's statement that the two sides have the same value at every $t \in R$: over a finite ring,
two different polynomials can take the same value at every point. `StarIdentity.eval` gives the
pointwise form. -/
def StarIdentity (j : ℤ) : Prop :=
  2 * X * W.Φ j * (W.Φ j + X * W.ΨSq j) + C W.b₂ * X * (W.Φ j * W.ΨSq j) +
      C W.b₄ * ((W.Φ j + X * W.ΨSq j) * W.ΨSq j) + C W.b₆ * W.ΨSq j ^ 2 =
    W.Φ (j + 1) * W.ΨSq (j - 1) + W.Φ (j - 1) * W.ΨSq (j + 1)

variable {W} in
theorem StarIdentity.eval {j : ℤ} (h : W.StarIdentity j) (t : R) :
    2 * t * (W.Φ j).eval t * ((W.Φ j).eval t + t * (W.ΨSq j).eval t) +
        W.b₂ * t * ((W.Φ j).eval t * (W.ΨSq j).eval t) +
        W.b₄ * (((W.Φ j).eval t + t * (W.ΨSq j).eval t) * (W.ΨSq j).eval t) +
        W.b₆ * (W.ΨSq j).eval t ^ 2 =
      (W.Φ (j + 1)).eval t * (W.ΨSq (j - 1)).eval t +
        (W.Φ (j - 1)).eval t * (W.ΨSq (j + 1)).eval t := by
  have h' := congrArg (Polynomial.eval t) h
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat] at h'
  exact h'

namespace Affine

variable {F : Type v} [Field F] {W : WeierstrassCurve F}

/-- **X-coordinate or zero.** For a point $P$ of a Weierstrass curve over a field $F$, the element
of $F$ that is $x$ when $P = (x, y)$ is affine and $0$ when $P$ is the point at infinity. Unlike
Mathlib's projective `Point.xRep`, it is a single element of $F$, as in the source's
multiplication-formula predicate. -/
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

/-- **Multiplication-formula predicate.** Let $P = (x, y)$ be a nonsingular affine point of a
Weierstrass curve $W$ over a field and let $m \in \mathbb{N}$, and let $\Phi_m$ and $\Psi_m^2$ be
the polynomials `W.Φ m` and `W.ΨSq m`. The predicate says that $\Psi_m^2(x) \ne 0$ and
$\operatorname{xCoordOrZero}(m \cdot P) \cdot \Psi_m^2(x) = \Phi_m(x)$, where `Point.xCoordOrZero`
is the $x$-coordinate of an affine point and $0$ at the point at infinity. It does not separately
require $m \cdot P$ to be affine: if $m \cdot P$ is the point at infinity, the equation says
$\Phi_m(x) = 0$. -/
def MFred [DecidableEq F] (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) : Prop :=
  (W.ΨSq (m : ℤ)).eval x ≠ 0 ∧
    (m • (Point.some x y h : W.toAffine.Point)).xCoordOrZero *
        (W.ΨSq (m : ℤ)).eval x =
      (W.Φ (m : ℤ)).eval x

/-- **Low-torsion freeness.** For a nonsingular affine point $P$ of a Weierstrass curve over a field
and $m \in \mathbb{N}$, no multiple $k \cdot P$ with $1 \le k \le m$ is the point at infinity. -/
def LowTorsionFree [DecidableEq F] (m : ℕ) {x y : F} (h : W.toAffine.Nonsingular x y) :
    Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ m → k • (Point.some x y h : W.toAffine.Point) ≠ 0

lemma LowTorsionFree.mono [DecidableEq F] {m n : ℕ} (hmn : m ≤ n) {x y : F}
    {h : W.toAffine.Nonsingular x y} (hf : LowTorsionFree n h) :
    LowTorsionFree m h :=
  fun k hk1 hkm => hf k hk1 (hkm.trans hmn)

section EvalLemmas

lemma eval_Φ_two (x : F) :
    (W.Φ 2).eval x = x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ := by
  simp [Φ_two]

/-- **Duplication denominator as a square.** Let $W$ be a Weierstrass curve over a field $F$. If
$x, y \in F$ satisfy the Weierstrass equation of $W$, then
$(y - \operatorname{negY}(x, y))^2 = \Psi_2^2(x)$, where
$\operatorname{negY}(x, y) = -y - a_1x - a_3$ is the $y$-coordinate of the negative of $(x, y)$ and
$\Psi_2^2$ is the polynomial `W.Ψ₂Sq`. This is Mathlib's `Affine.den_duplication_eq`, stated with
`Ψ₂Sq` and `negY`. -/
lemma sq_sub_negY_eq_eval_Ψ₂Sq {x y : F} (h : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = (W.Ψ₂Sq).eval x := by
  rw [Ψ₂Sq_eq, eval_toPoly_twoTorsionPolynomial, Affine.den_duplication_eq h, Affine.negY]
  ring

/-- **Duplication denominator is nonzero.** Let $W$ be a Weierstrass curve over a field $F$. If
$x, y \in F$ satisfy the Weierstrass equation of $W$ and $y \ne \operatorname{negY}(x, y)$, then
$\Psi_2^2(x) \ne 0$, where $\Psi_2^2$ is the polynomial `W.Ψ₂Sq`. This is one direction of
Mathlib's `Affine.den_duplication_eq_zero_iff`, stated with `Ψ₂Sq`. -/
lemma Ψ₂Sq_eval_ne_zero {x y : F} (h : W.toAffine.Equation x y)
    (hy : y ≠ W.toAffine.negY x y) : (W.Ψ₂Sq).eval x ≠ 0 := by
  rw [Ψ₂Sq_eq, eval_toPoly_twoTorsionPolynomial]
  exact (Affine.den_duplication_eq_zero_iff h).not.mpr hy

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

theorem addX_add_addX_negY_mul_sq {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) +
        W.toAffine.addX x₁ x₂
          (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
        (x₁ - x₂) ^ 2 =
      2 * (x₁ * x₂) * (x₁ + x₂) + W.b₂ * (x₁ * x₂) + W.b₄ * (x₁ + x₂) +
        W.b₆ := by
  have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have e₁ := (eq_div_iff hd2).mp
    (Affine.addX_of_X_ne (W := W.toAffine) (y₁ := y₁) (y₂ := y₂) hx)
  have e₂ := (eq_div_iff hd2).mp
    (Affine.addX_of_X_ne (W := W.toAffine) (y₁ := y₁) (y₂ := W.toAffine.negY x₂ y₂) hx)
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
  have e₁ := (eq_div_iff hd2).mp
    (Affine.addX_of_X_ne (W := W.toAffine) (y₁ := y₁) (y₂ := y₂) hx)
  have e₂ := (eq_div_iff hd2).mp
    (Affine.addX_of_X_ne (W := W.toAffine) (y₁ := y₁) (y₂ := W.toAffine.negY x₂ y₂) hx)
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

/-- **Doubling formula.** Let $W$ be a Weierstrass curve over a field $F$. If $x_1, y_1 \in F$
satisfy the Weierstrass equation of $W$ and $y_1 \ne \operatorname{negY}(x_1, y_1)$, then the
$x$-coordinate `addX x₁ x₁ (slope x₁ x₁ y₁ y₁)` of $(x_1, y_1) + (x_1, y_1)$, multiplied by
$\Psi_2^2(x_1)$, is $\Phi_2(x_1)$, where $\Psi_2^2$ and $\Phi_2$ are the polynomials `W.Ψ₂Sq` and
`W.Φ 2`. This is Mathlib's `Affine.addX_self_of_Y_ne` with the denominator cleared. -/
theorem addX_self_mul_Ψ₂Sq {x₁ y₁ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) *
        (W.Ψ₂Sq).eval x₁ =
      (W.Φ 2).eval x₁ := by
  rw [Affine.addX_self_of_Y_ne h₁ hy, eval_Φ_two, Ψ₂Sq_eq, eval_toPoly_twoTorsionPolynomial]
  exact div_mul_cancel₀ _ ((Affine.den_duplication_eq_zero_iff h₁).not.mpr hy)

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
