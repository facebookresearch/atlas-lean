/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.QuadraticForm.Isotropic
public import MathlibExt.NumberTheory.Rat.LocalGlobal

/-!
# The Hasse–Minkowski theorem for diagonal binary forms over `ℚ`

If $a x^2 + b y^2$ with $a, b \in \mathbb{Q}$ has a zero other than $(0, 0)$ over $\mathbb{R}$ and
over $\mathbb{Q}_p$ for every prime $p$, then it has one over $\mathbb{Q}$
(`Rat.exists_binary_eq_zero_of_forall_local`). Over each field the form has such a zero exactly
when $-ab$ is a square (`exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff`), and a rational number that
is a square in $\mathbb{R}$ and in every $\mathbb{Q}_p$ is a square in $\mathbb{Q}$
(`Rat.isSquare_of_isSquare_real_of_forall_isSquare_padic`).
-/

@[expose] public section

/-- **Hasse–Minkowski theorem for diagonal binary forms over $\mathbb{Q}$.** Let $a, b$ be rational
numbers. If $a x^2 + b y^2 = 0$ has a solution $(x, y) \neq (0, 0)$ in $\mathbb{R}^2$ and in
$\mathbb{Q}_p^2$ for every prime $p$, then it has a solution $(x, y) \neq (0, 0)$ in
$\mathbb{Q}^2$.

The source states it for $a, b \neq 0$; the Lean statement needs no such hypothesis, as the square
criterion `exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff` holds for all $a, b$.

Source: A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT, Fall 2013, Lecture
11, proof of Theorem 11.12, case $n = 2$, p. 4,
<https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>. -/
theorem Rat.exists_binary_eq_zero_of_forall_local {a b : ℚ}
    (hreal : ∃ x y : ℝ, (x, y) ≠ (0, 0) ∧ (a : ℝ) * x ^ 2 + b * y ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x y : ℚ_[p], (x, y) ≠ (0, 0) ∧
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 = 0) :
    ∃ x y : ℚ, (x, y) ≠ (0, 0) ∧ a * x ^ 2 + b * y ^ 2 = 0 := by
  rw [exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff] at hreal ⊢
  refine Rat.isSquare_of_isSquare_real_of_forall_isSquare_padic ?_ fun p _ => ?_
  · push_cast
    exact hreal
  · have h := hpadic p
    rw [exists_ne_zero_mul_sq_add_mul_sq_eq_zero_iff] at h
    push_cast
    exact h
