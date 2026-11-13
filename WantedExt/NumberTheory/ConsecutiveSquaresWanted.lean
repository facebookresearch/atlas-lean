/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Finite.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **The sum of consecutive squares equation.** Integers $a$, $b$, $c$ satisfy the sum of
consecutive squares (SoCS) equation when $2\,b(b+1)(2b+1) = a(a+1)(2a+1) + c(c+1)(2c+1)$.

With $P_n = n(n+1)(2n+1)/6$ this is $P_a + P_c = 2P_b$ multiplied by $6$. For $a < b < c$ it is
equivalent to $(a+1)^2 + (a+2)^2 + \dots + b^2 = (b+1)^2 + (b+2)^2 + \dots + c^2$, since
$P_n - P_{n-1} = n^2$. No order or sign condition on $a$, $b$, $c$ is imposed.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, equations (1) and (2). -/
public def SoCSEq (a b c : ℤ) : Prop :=
  2 * (b * (b + 1) * (2 * b + 1))
    = a * (a + 1) * (2 * a + 1) + c * (c + 1) * (2 * c + 1)

/-- **Solutions of the sum of consecutive squares problem.** A triple of integers
$(a, b, c)$ is a SoCS solution when $0 < a + 1 < b < c$ and $(a, b, c)$ satisfies the sum of
consecutive squares equation $2\,b(b+1)(2b+1) = a(a+1)(2a+1) + c(c+1)(2c+1)$, that is,
$(a+1)^2 + \dots + b^2 = (b+1)^2 + \dots + c^2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public def IsSoCSSolution (a b c : ℤ) : Prop :=
  0 < a + 1 ∧ a + 1 < b ∧ b < c ∧ SoCSEq a b c

/-- **$(2, 4, 5)$ solves the sum of consecutive squares problem.** The triple $(2, 4, 5)$ is a
solution of the sum of consecutive squares problem: $0 < 3 < 4 < 5$ and $3^2 + 4^2 = 5^2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public theorem isSoCSSolution_two_four_five : IsSoCSSolution 2 4 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold SoCSEq
  norm_num

/-- **Bounds on the ratio of the two spans.** For every solution $(a, b, c)$ of the sum of
consecutive squares problem, $1 < (b - a)/(c - b) < 1 + 2^{1/3} + 2^{2/3}$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Lemma 1
(`integers-2026-A1-lem-1`). -/
public theorem_wanted soCS_ratio_bounds (a b c : ℤ) (h : IsSoCSSolution a b c) :
    1 < (b - a : ℝ) / (c - b) ∧
    (b - a : ℝ) / (c - b) < 1 + (2 : ℝ) ^ (1 / 3 : ℝ) + (2 : ℝ) ^ (2 / 3 : ℝ)

/-- **The Pell-type parameter is a positive nonsquare.** For every solution $(a, b, c)$ of the
sum of consecutive squares problem, the integer
$A = 3(b - c)^2\bigl(12(b - a)^2(c - b)^2 - (a - 2b + c)^4\bigr)$ is positive and is not a
perfect square.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 1
(`integers-2026-A1-cor-1`), verified against arXiv:2411.08398 (the formula
is garbled in the statement extraction). -/
public theorem_wanted soCS_pell_param_pos_nonsquare (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    0 < 3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4) ∧
    ¬ IsSquare (3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4))

/-- **Infinite families of solutions in a plane.** Let $(a, b, c)$ be a solution of the sum of
consecutive squares problem. Then there are infinitely many distinct integer triples $(x, y, z)$
satisfying the sum of consecutive squares equation
$2\,y(y+1)(2y+1) = x(x+1)(2x+1) + z(z+1)(2z+1)$, with no order or sign condition, such that
$(b - c)x + (c - a)y + (a - b)z = 0$ and $z - x \equiv c - a \pmod 2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Proposition 1
(`integers-2026-A1-prop-1`). -/
public theorem_wanted soCS_infinite_family_plane (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0 ∧
        (f n).2.2 - (f n).1 ≡ c - a [ZMOD 2]

/-- **Solutions with odd span $c - a$.** For every odd integer $N \ge 3$ there is a solution
$(a, b, c)$ of the sum of consecutive squares problem with $c - a = N$, together with infinitely
many distinct solutions $(x, y, z)$ of that problem with $z - x$ odd, all lying in the plane
$(b - c)x + (c - a)y + (a - b)z = 0$, which passes through $(a, b, c)$ and contains the line
$x = y = z$.

The paper also states that this plane is unique for each $N$; that uniqueness clause is not part
of this statement.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 2
(`integers-2026-A1-thm-2`), verified against arXiv:2411.08398. -/
public theorem_wanted soCS_odd_span (N : ℤ) (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧ c - a = N ∧
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, IsSoCSSolution (f n).1 (f n).2.1 (f n).2.2 ∧
        Odd ((f n).2.2 - (f n).1) ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0

/-- **Infinitely many solutions with $c - a$ even.** There are infinitely many solutions
$(a, b, c)$ of the sum of consecutive squares problem with $c - a$ even.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 3
(`integers-2026-A1-thm-3`). -/
public theorem_wanted soCS_even_span_infinite :
    {t : ℤ × ℤ × ℤ | IsSoCSSolution t.1 t.2.1 t.2.2 ∧ Even (t.2.2 - t.1)}.Infinite

/-- **At most $2(N - 1)$ solutions with $c - a = N$.** For every integer $N > 1$,
there are at most $2(N - 1)$ solutions $(a, b, c)$ of the sum of consecutive squares problem
with $c - a = N$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 5
(`integers-2026-A1-thm-5`). -/
public theorem_wanted soCS_card_le (N : ℤ) (hN : 1 < N)
    (s : Finset (ℤ × ℤ × ℤ))
    (hs : ∀ t ∈ s, IsSoCSSolution t.1 t.2.1 t.2.2 ∧ t.2.2 - t.1 = N) :
    s.card ≤ 2 * (N - 1).toNat

/-- **No finitely many planes contain all solutions.** Let $S$ be a finite set of affine planes
$ux + vy + wz = t$ in $\mathbb{R}^3$, with $u, v, w, t$ real and $(u, v, w) \ne (0, 0, 0)$. Then
some solution $(a, b, c)$ of the sum of consecutive squares problem lies on none of the planes in
$S$, that is, $ua + vb + wc \ne t$ for every plane in $S$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2
(`integers-2026-A1-cor-2`); the proof text appended to the extracted
statement is not part of the claim. -/
public theorem_wanted soCS_not_finite_planes
    (S : Finset (ℝ × ℝ × ℝ × ℝ))
    (hS : ∀ p ∈ S, (p.1, p.2.1, p.2.2.1) ≠ 0) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      ∀ p ∈ S, p.1 * (a : ℝ) + p.2.1 * (b : ℝ) + p.2.2.1 * (c : ℝ) ≠ p.2.2.2

end

end MetaMathlibExt
