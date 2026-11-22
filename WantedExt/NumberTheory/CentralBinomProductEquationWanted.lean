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

/-- Theorem 1: for positive `x`, `b` and nonnegative `a`,
`C(2(a+b), a+b) = C(2a, a) C(x+2b, b)` holds if and only if `x = a = 1`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Theorem 1 (`integers-2026-A26-thm-1`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_iff (x a b : ℕ) (hx : 0 < x)
    (hb : 0 < b) :
    (a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1

/-- Proposition 1: for positive `x`, `b`, nonnegative `a` and `x ≥ a`,
`C(2(a+b), a+b) ≤ C(2a, a) C(x+2b, b)`, with equality if and only if `x = a = 1`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 1 (`integers-2026-A26-prop-1`). -/
public theorem_wanted centralBinom_add_le_centralBinom_mul_choose_of_le (x a b : ℕ) (hx : 0 < x)
    (hb : 0 < b) (hax : a ≤ x) :
    (a + b).centralBinom ≤ a.centralBinom * (x + 2 * b).choose b ∧
      ((a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1)

/-- Lemma 1: for positive `x`, `a`, `b` with `a + b ≤ 10`,
`C(2(a+b), a+b) = C(2a, a) C(x+2b, b)` if and only if `x = a = 1`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 1 (`integers-2026-A26-lem-1`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_iff_of_le_ten (x a b : ℕ)
    (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hk : a + b ≤ 10) :
    (a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1

/-- Lemma 2: for positive `a`, `b` with `4 < 2a ≤ a + b`,
`C(2(a+b), a+b) ≠ C(2a, a) C(a+2b-1, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 2 (`integers-2026-A26-lem-2`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_one (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 1).choose b

/-- Lemma 3: for positive `a`, `b` with `4 < 2a ≤ a + b`,
`C(2(a+b), a+b) ≠ C(2a, a) C(a+2b-2, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 3 (`integers-2026-A26-lem-3`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_two (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 2).choose b

/-- Lemma 4: for positive `a`, `b` with `4 < 2a ≤ a + b`,
`C(2(a+b), a+b) ≠ C(2a, a) C(a+2b-3, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 4 (`integers-2026-A26-lem-4`). -/
public theorem_wanted centralBinom_add_ne_centralBinom_mul_choose_sub_three (a b : ℕ)
    (ha : 4 < 2 * a) (hab : 2 * a ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (a + 2 * b - 3).choose b

/-- Lemma 5 (Hanson): for `0 < m < n`, the product `n (n+1) ⋯ (n+m-1)` has a prime divisor
`p > 3m/2` if and only if `(n, m)` is none of the exceptions `3·4`, `8·9`,
`6·7·8·9·10`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 5 (`integers-2026-A26-lem-5`), quoting Hanson. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_three_halves_iff (n m : ℕ)
    (hm : 0 < m) (hmn : m < n) :
    (∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 3 * m < 2 * p) ↔
      (n, m) ≠ (3, 2) ∧ (n, m) ≠ (8, 2) ∧ (n, m) ≠ (6, 5)

/-- Lemma 6 (Stănică): for positive integers `m > r ≥ 1` and `n ≥ 1`, with
`B = m^(mn+1/2) / ((m-r)^((m-r)n+1/2) r^(rn+1/2))`,
`e^(-1/(8n)) n^(-1/2) B / √(2π) < C(mn, rn) < n^(-1/2) B / √(2π)`.

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

/-- Lemma 7: for positive `x`, `a`, `b` with `a ≥ (a+b)/2` and `b ≥ 3`,
`C(2(a+b), a+b) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 7 (`integers-2026-A26-lem-7`). -/
public theorem_wanted centralBinom_add_ne_of_half_le_of_three_le (x a b : ℕ) (hx : 0 < x)
    (hab : a + b ≤ 2 * a) (hb : 3 ≤ b) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- Lemma 8: for positive `a`, `b` and `x ≥ 2` with `a ≥ (a+b)/2`,
`C(2(a+b), a+b) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 8 (`integers-2026-A26-lem-8`). -/
public theorem_wanted centralBinom_add_ne_of_half_le_of_two_le (x a b : ℕ) (hx : 2 ≤ x)
    (hb : 0 < b) (hab : a + b ≤ 2 * a) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- Lemma 9 (Shanta-Shorey): if `n > m > 2` and `n + m ≥ 150`, then
`n (n+1) ⋯ (n+m-1)` has a prime divisor `p > 1.8 m`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 9 (`integers-2026-A26-lem-9`), quoting Shanta and
Shorey. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_nine_fifths (n m : ℕ) (hm : 2 < m)
    (hmn : m < n) (h150 : 150 ≤ n + m) :
    ∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 9 * m < 5 * p

/-- Lemma 10 (Nair-Shorey): if `n > 4m`, `m > 3` and `n + m ≥ 150`, then
`n (n+1) ⋯ (n+m-1)` has a prime divisor `p > 4.42 m`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 10 (`integers-2026-A26-lem-10`), quoting Nair and
Shorey. -/
public theorem_wanted exists_prime_dvd_prod_consecutive_gt_four_point_four_two (n m : ℕ)
    (hm : 3 < m) (hmn : 4 * m < n) (h150 : 150 ≤ n + m) :
    ∃ p, p.Prime ∧ p ∣ ∏ i ∈ range m, (n + i) ∧ 442 * m < 100 * p

/-- Lemma 11: for positive `a`, `b`, `x ≥ 2` with `k = a + b ≥ 75`, `a ≤ 0.9 k` and
`b ≤ 0.8 k`, `C(2k, k) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 11 (`integers-2026-A26-lem-11`). -/
public theorem_wanted centralBinom_add_ne_of_balanced (x a b : ℕ) (hx : 2 ≤ x) (ha : 0 < a)
    (hb : 0 < b) (hk : 75 ≤ a + b) (ha9 : 10 * a ≤ 9 * (a + b)) (hb8 : 5 * b ≤ 4 * (a + b)) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- Lemma 12: for positive `b`, `x ≥ 2`, `a + b ≥ 150` and `a ≥ (171/121) x`,
`C(2(a+b), a+b) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 12 (`integers-2026-A26-lem-12`). -/
public theorem_wanted centralBinom_add_ne_of_large_a (x a b : ℕ) (hx : 2 ≤ x) (hb : 0 < b)
    (hk : 150 ≤ a + b) (ha : 171 * x ≤ 121 * a) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- Proposition 2: for positive `a`, `b`, `C(2(a+b), a+b) = C(2a, a) C(1+2b, b)` if and only
if `a = 1`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 2 (`integers-2026-A26-prop-2`). -/
public theorem_wanted centralBinom_add_eq_centralBinom_mul_choose_one_iff (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) :
    (a + b).centralBinom = a.centralBinom * (1 + 2 * b).choose b ↔ a = 1

/-- Proposition 3: for positive `a`, `b`, `x ≥ 2` and `a + b ≥ 150`,
`C(2(a+b), a+b) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 3 (`integers-2026-A26-prop-3`). -/
public theorem_wanted centralBinom_add_ne_of_two_le_of_large (x a b : ℕ) (hx : 2 ≤ x)
    (ha : 0 < a) (hb : 0 < b) (hk : 150 ≤ a + b) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

/-- Proposition 4: for positive `a`, `b`, `x ≥ 2` and `x < a + b < 150`,
`C(2(a+b), a+b) ≠ C(2a, a) C(x+2b, b)`.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Proposition 4 (`integers-2026-A26-prop-4`). -/
public theorem_wanted centralBinom_add_ne_of_two_le_of_small (x a b : ℕ) (hx : 2 ≤ x)
    (ha : 0 < a) (hb : 0 < b) (hxk : x < a + b) (hk : a + b < 150) :
    (a + b).centralBinom ≠ a.centralBinom * (x + 2 * b).choose b

end

end MetaMathlibExt
