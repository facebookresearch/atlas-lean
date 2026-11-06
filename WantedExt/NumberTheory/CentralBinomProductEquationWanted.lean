/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Solvability of `C(2k, k) = C(2a, a) C(x + 2b, b)`

Statements from Meaghan Allen, *Solvability of
$\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*, INTEGERS 26 (2026), Article A26
(arXiv 2406.10404). Throughout, `k = a + b` is substituted, `C(2k, k)` is
`Nat.centralBinom`, and the prime-factor lemmas quoted from Hanson, Shanta-Shorey and
Nair-Shorey are stated for `∏_{i<m} (n + i) = n (n+1) ⋯ (n+m-1)`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Allen's theorem on central binomial products.** Let $x$ and $b$ be positive integers and
let $a$ be a nonnegative integer. Then $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ if
and only if $x = 1$ and $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Theorem 1 (`integers-2026-A26-thm-1`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_iff (x a b : ℕ) (hx : 0 < x)
    (hb : 0 < b) :
    (a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1

/-- **Allen's inequality for central binomial products.** Let $x$ and $b$ be positive integers
and let $a$ be a nonnegative integer with $a \le x$. Then
$\binom{2(a+b)}{a+b} \le \binom{2a}{a}\binom{x+2b}{b}$, and equality holds if and only if
$x = 1$ and $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 1 (`integers-2026-A26-prop-1`). -/
public theorem_wanted centralBinom_add_le_centralBinom_mul_choose_of_le (x a b : ℕ) (hx : 0 < x)
    (hb : 0 < b) (hax : a ≤ x) :
    (a + b).centralBinom ≤ a.centralBinom * (x + 2 * b).choose b ∧
      ((a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1)

/-- **Central binomial products with $a + b \le 10$.** Let $x$, $a$, $b$ be positive integers
with $a + b \le 10$. Then $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ if and only if
$x = 1$ and $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 1 (`integers-2026-A26-lem-1`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_iff_of_le_ten (x a b : ℕ)
    (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hk : a + b ≤ 10) :
    (a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1

/-- **Central binomial products in the case $x = a - 1$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-1}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 2 (`integers-2026-A26-lem-2`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_one (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 1).choose b

/-- **Central binomial products in the case $x = a - 2$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-2}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 2$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 3 (`integers-2026-A26-lem-3`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_two (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 2).choose b

/-- **Central binomial products in the case $x = a - 3$.** Let $a$ and $b$ be natural numbers
with $4 < 2a \le a + b$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{a+2b-3}{b}$, so the
equation $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ has no solution with $x = a - 3$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 4 (`integers-2026-A26-lem-4`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_three (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 3).choose b

/-- **Hanson's theorem on a prime factor above $3m/2$ in consecutive integers.** Let $m$ and $n$
be natural numbers with $0 < m < n$. The product $n(n+1)\cdots(n+m-1)$ has a prime divisor $p$
with $p > 3m/2$ if and only if $(n, m)$ is none of the pairs $(3, 2)$, $(8, 2)$ and $(6, 5)$
(the products $3 \cdot 4$, $8 \cdot 9$ and $6 \cdot 7 \cdot 8 \cdot 9 \cdot 10$).

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 5 (`integers-2026-A26-lem-5`), quoting Hanson. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_three_halves_iff (n m : ℕ)
    (hm : 0 < m) (hmn : m < n) :
    (∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 3 * m < 2 * p) ↔
      (n, m) ≠ (3, 2) ∧ (n, m) ≠ (8, 2) ∧ (n, m) ≠ (6, 5)

/-- **Stănică's bounds for the binomial coefficient $\binom{mn}{rn}$.** Let $m$, $n$ and $r$ be
natural numbers with $1 \le r < m$ and $n \ge 1$, and put

$$B = \frac{m^{mn + 1/2}}{(m-r)^{(m-r)n + 1/2}\, r^{rn + 1/2}}.$$

Then

$$\frac{e^{-1/(8n)}}{\sqrt{2\pi}\,\sqrt{n}}\, B < \binom{mn}{rn} <
\frac{1}{\sqrt{2\pi}\,\sqrt{n}}\, B.$$

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 6 (`integers-2026-A26-lem-6`), quoting Stănică. -/
public theorem_wanted choose_mul_mul_bounds (m n r : ℕ) (hr : 1 ≤ r) (hrm : r < m)
    (hn : 1 ≤ n) :
    Real.exp (-(1 / (8 * (n : ℝ)))) / (Real.sqrt (2 * Real.pi) * Real.sqrt n) *
          ((m : ℝ) ^ (m * n) * Real.sqrt m /
            (((m - r : ℕ) : ℝ) ^ ((m - r) * n) * Real.sqrt ((m - r : ℕ) : ℝ) *
              ((r : ℝ) ^ (r * n) * Real.sqrt r))) <
        ((m * n).choose (r * n) : ℝ) ∧
      ((m * n).choose (r * n) : ℝ) <
        1 / (Real.sqrt (2 * Real.pi) * Real.sqrt n) *
          ((m : ℝ) ^ (m * n) * Real.sqrt m /
            (((m - r : ℕ) : ℝ) ^ ((m - r) * n) * Real.sqrt ((m - r : ℕ) : ℝ) *
              ((r : ℝ) ^ (r * n) * Real.sqrt r)))

/-- **Central binomial products with $a \ge b \ge 3$.** Let $x$, $a$, $b$ be natural numbers with
$x \ge 1$ and $3 \le b \le a$. Then $\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 7 (`integers-2026-A26-lem-7`). -/
public theorem_wanted centralBinom_add_ne_of_half_le_of_three_le (x a b : ℕ) (hx : 0 < x)
    (hab : a + b ≤ 2 * a) (hb : 3 ≤ b) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- **Central binomial products with $x \ge 2$ and $a \ge b$.** Let $x$, $a$, $b$ be natural
numbers with $x \ge 2$ and $1 \le b \le a$. Then
$\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 8 (`integers-2026-A26-lem-8`). -/
public theorem_wanted centralBinom_add_ne_of_half_le_of_two_le (x a b : ℕ) (hx : 2 ≤ x)
    (hb : 0 < b) (hab : a + b ≤ 2 * a) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- **A prime factor above $9m/5$ in a product of consecutive integers.** Let $m$ and $n$ be
natural numbers with $2 < m < n$ and $n + m \ge 150$. Then the product $n(n+1)\cdots(n+m-1)$ has
a prime divisor $p$ with $p > 9m/5$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 9 (`integers-2026-A26-lem-9`), quoting Shanta and
Shorey. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_nine_fifths (n m : ℕ) (hm : 2 < m)
    (hmn : m < n) (h150 : 150 ≤ n + m) :
    ∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 9 * m < 5 * p

/-- **A prime factor above $4.42m$ in a product of consecutive integers.** Let $m$ and $n$ be
natural numbers with $m > 3$, $n > 4m$ and $n + m \ge 150$. Then the product
$n(n+1)\cdots(n+m-1)$ has a prime divisor $p$ with $p > 4.42\,m$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 10 (`integers-2026-A26-lem-10`), quoting Nair and
Shorey. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_four_point_four_two (n m : ℕ)
    (hm : 3 < m) (hmn : 4 * m < n) (h150 : 150 ≤ n + m) :
    ∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 442 * m < 100 * p

/-- **Central binomial products in the balanced range.** Let $a$ and $b$ be positive integers,
let $x \ge 2$ be an integer, and put $k = a + b$. If $k \ge 75$, $a \le \tfrac{9}{10}k$ and
$b \le \tfrac{4}{5}k$, then $\binom{2k}{k} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 11 (`integers-2026-A26-lem-11`). -/
public theorem_wanted centralBinom_add_ne_of_balanced (x a b : ℕ) (hx : 2 ≤ x) (ha : 0 < a)
    (hb : 0 < b) (hk : 75 ≤ a + b) (ha9 : 10 * a ≤ 9 * (a + b)) (hb8 : 5 * b ≤ 4 * (a + b)) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- **No large solutions of the central binomial product equation with a dominant central factor.**
For natural numbers $a$, $b$, $x$ with $b \ge 1$, $x \ge 2$, $a + b \ge 150$ and
$a \ge \frac{171}{121} x$, we have
$\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 12 (`integers-2026-A26-lem-12`). -/
public theorem_wanted centralBinom_add_ne_of_large_a (x a b : ℕ) (hx : 2 ≤ x) (hb : 0 < b)
    (hk : 150 ≤ a + b) (ha : 171 * x ≤ 121 * a) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- **Central binomial products with $x = 1$.** Let $a$ and $b$ be positive integers. Then
$\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{1+2b}{b}$ if and only if $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 2 (`integers-2026-A26-prop-2`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_one_iff (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) :
    (a + b).centralBinom = a.centralBinom * (1 + 2 * b).choose b ↔ a = 1

/-- **No large solutions of the central binomial product equation with shift at least two.**
For natural numbers $a$, $b$, $x$ with $a \ge 1$, $b \ge 1$, $x \ge 2$ and $a + b \ge 150$, we have
$\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 3 (`integers-2026-A26-prop-3`). -/
public theorem_wanted centralBinom_add_ne_of_two_le_of_large (x a b : ℕ) (hx : 2 ≤ x)
    (ha : 0 < a) (hb : 0 < b) (hk : 150 ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- **Central binomial products with $x \ge 2$ and $a + b < 150$.** Let $x$, $a$, $b$ be natural
numbers with $a \ge 1$, $b \ge 1$, $x \ge 2$ and $x < a + b < 150$. Then
$\binom{2(a+b)}{a+b} \ne \binom{2a}{a}\binom{x+2b}{b}$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 4 (`integers-2026-A26-prop-4`). -/
public theorem_wanted centralBinom_add_ne_of_two_le_of_small (x a b : ℕ) (hx : 2 ≤ x)
    (ha : 0 < a) (hb : 0 < b) (hxk : x < a + b) (hk : a + b < 150) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

end

end MetaMathlibExt
