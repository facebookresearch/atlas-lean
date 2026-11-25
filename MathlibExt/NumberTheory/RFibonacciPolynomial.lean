/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Separability of the characteristic polynomial of the (-r)-Fibonacci recurrence -/

namespace MetaMathlibExt

open Polynomial

/-- **Separability of $t^{r+1} - y^{-1} t + x y^{-1}$.** Let $K$ be a field of characteristic zero,
let $r \ge 1$, let $x \in K$ and let $y \in K$ be nonzero with $(r+1)^{r+1} x^r y \ne r^r$. Then
the polynomial $t^{r+1} - y^{-1} t + x y^{-1} \in K[t]$ is separable, that is, coprime to its
derivative; equivalently, it has no multiple zeros in an algebraic closure of $K$.

This corrects Lemma 1 of the paper. The printed hypothesis $x \ne \frac{r}{r+1} ((r+1) y)^{-1/r}$
names only one $r$-th root and is insufficient: $r = 2$, $y = 1/3$, $x = -2/3$ satisfies it, since
$\frac{2}{3} \cdot 1^{-1/2} = \frac{2}{3}$, yet $t^3 - 3t - 2 = (t + 1)^2 (t - 2)$. The paper's
proof shows that a multiple zero $\beta$ forces $x = r\beta/(r+1)$ with $\beta^r = 1/((r+1) y)$,
that is, $(r+1)^{r+1} x^r y = r^r$, which is the branch-free condition used here.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Lemma 1 (`integers-2025-A38-lem-1`). -/
public theorem separable_negRFibonacci_charPoly {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (hr : 1 ≤ r) (x : K) (y : Kˣ)
    (h : ((r : K) + 1) ^ (r + 1) * x ^ r * y ≠ (r : K) ^ r) :
    (Polynomial.X ^ (r + 1) - Polynomial.C (↑y⁻¹ : K) * Polynomial.X
      + Polynomial.C (x * ↑y⁻¹) : Polynomial K).Separable := by
  let f := algebraMap K (AlgebraicClosure K)
  have hy : f (y : K) ≠ 0 := (map_ne_zero f).mpr y.ne_zero
  have hr' : (r : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  rw [separable_def, isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)]
  intro β
  rw [← not_and_or]
  rintro ⟨hp, hd⟩
  rw [derivative_add, derivative_sub, derivative_X_pow_succ, derivative_C_mul_X, derivative_C,
    add_zero] at hd
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_natCast, map_one,
    Units.val_inv_eq_inv_val, map_inv₀] at hp hd
  field_simp [hy] at hp hd
  -- Eliminate the leading power using the derivative at the common root.
  have hβ : β = ((r : AlgebraicClosure K) + 1) * f x / r := by
    apply (eq_div_iff hr').2
    linear_combination β * hd - ((r : AlgebraicClosure K) + 1) * hp
  apply h
  apply f.injective
  simp only [map_mul, map_pow, map_add, map_natCast, map_one]
  rw [hβ, div_pow, mul_pow] at hd
  field_simp [hr'] at hd
  linear_combination hd

end MetaMathlibExt
