/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.LucasSequence
public import WantedExt.NumberTheory.HyperLeonardoWanted

/-!
# Hypersequences of an arbitrary sequence and their weighted sums (Parisse)

Statements from Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their
Weighted Sums*, INTEGERS 24 (2024), Article A70.

Conventions. The hypersequence `a^{(r)}_n` is `hypersequence a r n`; the hyperfibonacci numbers
are the existing `hyperFibonacci` (bridge `hyperFibonacci_eq_hypersequence`), the Lucas numbers
are `lucasNumber` and the hyperlucas numbers are `hypersequence lucasNumber`. The paper's
sequences are complex; general statements use `ℂ`. `p_{ℓ,m}(x, y)` is
`alternatingBinomialPowerSum ℓ m x y`, and `c_{ℓ,m}(n) = p_{ℓ,m}(1, n + 1)`. `S(j, m)` is
`Nat.stirlingSecond`. The weighted sums `t^{(r)}_ℓ(n) = ∑_{k=0}^{n} k^ℓ a^{(r)}_k` are written
out (with `0^0 = 1`, as in the paper). Binomial coefficients `C(x, k)` with a possibly negative
upper argument are `Ring.choose` over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The hypersequence of the `r`th generation: `a^{(0)}_n = a_n` and
`a^{(r)}_n = ∑_{k=0}^{n} a^{(r-1)}_k`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public def hypersequence {R : Type*} [AddCommMonoid R] (a : ℕ → R) : ℕ → ℕ → R
  | 0, n => a n
  | r + 1, n => ∑ k ∈ range (n + 1), hypersequence a r k

/-- `a^{(r+1)}_n = ∑_{k=0}^{n} a^{(r)}_k`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_succ {R : Type*} [AddCommMonoid R] (a : ℕ → R) (r n : ℕ) :
    hypersequence a (r + 1) n = ∑ k ∈ range (n + 1), hypersequence a r k :=
  rfl

/-- `a^{(1)}_0 = a_0`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_one_zero {R : Type*} [AddCommMonoid R] (a : ℕ → R) :
    hypersequence a 1 0 = a 0 := by
  simp [hypersequence]

/-- The existing hyperfibonacci numbers are the hypersequence of the Fibonacci numbers.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Example 3 (hyperfibonacci numbers). -/
public theorem hyperFibonacci_eq_hypersequence (r n : ℕ) :
    hyperFibonacci r n = hypersequence Nat.fib r n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp [hyperFibonacci, hypersequence, ih]

/-- `p_{ℓ,m}(x, y) = ∑_{k=0}^{m} (-1)^k C(m, k) (k x + y)^ℓ`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public def alternatingBinomialPowerSum (ℓ m : ℕ) (x y : ℂ) : ℂ :=
  ∑ k ∈ range (m + 1), (-1) ^ k * (m.choose k : ℂ) * (k * x + y) ^ ℓ

/-- `p_{1,1}(1, 1) = 1 - 2 = -1`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 3, Equation (3.9). -/
public theorem alternatingBinomialPowerSum_one_one_one_one :
    alternatingBinomialPowerSum 1 1 1 1 = -1 := by
  simp [alternatingBinomialPowerSum, sum_range_succ]

/-- Theorem 1: for `r ≥ 1`,
`a^{(r)}_n = ∑_{k=0}^{n} C(n + r - 1 - k, r - 1) a_k = ∑_{k=0}^{n} C(r + k - 1, k) a_{n-k}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 1, Equation (2.1) (`integers-2024-A70-thm-1`). -/
public theorem_wanted hypersequence_eq_sum_choose (a : ℕ → ℂ) {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    hypersequence a r n = ∑ k ∈ range (n + 1), ((n + r - 1 - k).choose (r - 1) : ℂ) * a k ∧
      hypersequence a r n = ∑ k ∈ range (n + 1), ((r + k - 1).choose k : ℂ) * a (n - k)

/-- Theorem 2: `a^{(r+1)}_{n+1} = a^{(r+1)}_n + a^{(r)}_{n+1}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 2, Equation (2.2) (`integers-2024-A70-thm-2`). -/
public theorem_wanted hypersequence_succ_succ (a : ℕ → ℂ) (r n : ℕ) :
    hypersequence a (r + 1) (n + 1) = hypersequence a (r + 1) n + hypersequence a r (n + 1)

/-- Theorem 3: `F^{(r)}_n = F_{n+2r} - ∑_{k=0}^{r-1} C(n + k - 1, k) F_{2(r-k)}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 3, Equation (2.8) (`integers-2024-A70-thm-3`). -/
public theorem_wanted hyperFibonacci_eq_fib_sub_sum (r n : ℕ) :
    (hyperFibonacci r n : ℤ) =
      Nat.fib (n + 2 * r) - ∑ k ∈ range r, ((n + k - 1).choose k * Nat.fib (2 * (r - k)) : ℕ)

/-- Corollary 1: for `r ≥ 1`,
`F_{n+2r} = ∑_{k=0}^{n} C(n + r - 1 - k, r - 1) F_k + ∑_{k=0}^{r-1} C(n + k - 1, k) F_{2(r-k)}`,
and the same with `∑_{k=0}^{n} C(r + k - 1, k) F_{n-k}` as first sum.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 1 (`integers-2024-A70-cor-1`). -/
public theorem_wanted fib_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * Nat.fib k +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k)) ∧
      Nat.fib (n + 2 * r) = ∑ k ∈ range (n + 1), (r + k - 1).choose k * Nat.fib (n - k) +
        ∑ k ∈ range r, (n + k - 1).choose k * Nat.fib (2 * (r - k))

/-- Theorem 4 (Cristea–Martinjak–Urbiha, as quoted): `F^{(r)}_0 = 0`, `F^{(r)}_1 = 1`, and for
`r ≥ 1`, `F^{(r)}_{n+2} = F^{(r)}_{n+1} + F^{(r)}_n + C(n + r, r - 1)` (written for `r + 1`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 4, Equation (2.9) (`integers-2024-A70-thm-4`). -/
public theorem_wanted hyperFibonacci_recurrence (r n : ℕ) :
    hyperFibonacci r 0 = 0 ∧ hyperFibonacci r 1 = 1 ∧
      hyperFibonacci (r + 1) (n + 2) =
        hyperFibonacci (r + 1) (n + 1) + hyperFibonacci (r + 1) n + (n + r + 1).choose r

/-- Theorem 5: `L^{(r)}_n = L_{n+2r} - ∑_{k=0}^{r-1} C(n + k, k) L_{2(r-k)-1}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 5, Equation (2.12) (`integers-2024-A70-thm-5`). -/
public theorem_wanted hyperLucas_eq_lucas_sub_sum (r n : ℕ) :
    ((hypersequence lucasNumber r n : ℕ) : ℤ) =
      lucasNumber (n + 2 * r) -
        ∑ k ∈ range r, ((n + k).choose k * lucasNumber (2 * (r - k) - 1) : ℕ)

/-- Corollary 2: for `r ≥ 1`,
`L_{n+2r} = ∑_{k=0}^{n} C(n + r - 1 - k, r - 1) L_k + ∑_{k=0}^{r-1} C(n + k, k) L_{2(r-k)-1}`,
and the same with `∑_{k=0}^{n} C(r + k - 1, k) L_{n-k}` as first sum.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 2 (`integers-2024-A70-cor-2`). -/
public theorem_wanted lucas_add_two_mul_eq_sum_choose {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (n + r - 1 - k).choose (r - 1) * lucasNumber k +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1) ∧
      lucasNumber (n + 2 * r) =
        ∑ k ∈ range (n + 1), (r + k - 1).choose k * lucasNumber (n - k) +
          ∑ k ∈ range r, (n + k).choose k * lucasNumber (2 * (r - k) - 1)

/-- Theorem 6: `L^{(r)}_0 = 2`, `L^{(r)}_1 = 2r + 1`, and for `r ≥ 1`,
`L^{(r)}_{n+2} = L^{(r)}_{n+1} + L^{(r)}_n + (n + 2r)/(n + 2) · C(n + r, r - 1)` (written for
`r + 1`, in `ℚ`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 6, Equation (2.13) (`integers-2024-A70-thm-6`). -/
public theorem_wanted hyperLucas_recurrence (r n : ℕ) :
    hypersequence lucasNumber r 0 = 2 ∧ hypersequence lucasNumber r 1 = 2 * r + 1 ∧
      ((hypersequence lucasNumber (r + 1) (n + 2) : ℕ) : ℚ) =
        ((hypersequence lucasNumber (r + 1) (n + 1) : ℕ) : ℚ) +
          ((hypersequence lucasNumber (r + 1) n : ℕ) : ℚ) +
          ((n + 2 * (r + 1) : ℕ) : ℚ) / (n + 2) * ((n + r + 1).choose r : ℚ)

/-- Theorem 7 (Abel's summation by parts):
`∑_{k=0}^{n} a_k b_k = a^{(1)}_n b_{n+1} + ∑_{k=0}^{n} a^{(1)}_k (b_k - b_{k+1})`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 7 (`integers-2024-A70-thm-7`). -/
public theorem_wanted sum_mul_eq_hypersequence_one_mul_add_sum (a b : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * b k =
      hypersequence a 1 n * b (n + 1) + ∑ k ∈ range (n + 1), hypersequence a 1 k * (b k - b (k + 1))

/-- Theorem 8: `t^{(r)}_ℓ(n) = (n + 1)^ℓ a^{(r+1)}_n - ∑_{j=0}^{ℓ-1} C(ℓ, j) t^{(r+1)}_j(n)`,
with `t^{(r)}_ℓ(n) = ∑_{k=0}^{n} k^ℓ a^{(r)}_k` (so `t^{(r)}_0(n) = a^{(r+1)}_n`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 8, Equation (3.5) (`integers-2024-A70-thm-8`). -/
public theorem_wanted sum_pow_mul_hypersequence_recurrence (a : ℕ → ℂ) (ℓ r n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
      ((n : ℂ) + 1) ^ ℓ * hypersequence a (r + 1) n -
        ∑ j ∈ range ℓ, (ℓ.choose j : ℂ) *
          ∑ k ∈ range (n + 1), (k : ℂ) ^ j * hypersequence a (r + 1) k

/-- Theorem 9: `t^{(r)}_ℓ(n) = ∑_{m=0}^{ℓ} c_{ℓ,m}(n) a^{(r+m+1)}_n
= ∑_{j=0}^{ℓ} C(ℓ, j) (∑_{m=0}^{j} (-1)^m m! S(j, m) a^{(r+m+1)}_n) (n + 1)^{ℓ-j}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 9, Equations (3.7) and (3.8)
(`integers-2024-A70-thm-9`). -/
public theorem_wanted sum_pow_mul_hypersequence_eq (a : ℕ → ℂ) (ℓ n r : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
        ∑ m ∈ range (ℓ + 1),
          alternatingBinomialPowerSum ℓ m 1 (n + 1) * hypersequence a (r + m + 1) n ∧
      ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * hypersequence a r k =
        ∑ j ∈ range (ℓ + 1), (ℓ.choose j : ℂ) *
          (∑ m ∈ range (j + 1), (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond j m : ℂ) *
            hypersequence a (r + m + 1) n) * ((n : ℂ) + 1) ^ (ℓ - j)

/-- Corollary 3 (Theorem 9 for `r = 0`): `t_ℓ(n) = ∑_{m=0}^{ℓ} c_{ℓ,m}(n) a^{(m+1)}_n
= ∑_{j=0}^{ℓ} C(ℓ, j) (∑_{m=0}^{j} (-1)^m m! S(j, m) a^{(m+1)}_n) (n + 1)^{ℓ-j}`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 3 (`integers-2024-A70-cor-3`). -/
public theorem_wanted sum_pow_mul_eq (a : ℕ → ℂ) (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * a k =
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 (n + 1) * hypersequence a (m + 1) n ∧
      ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * a k =
        ∑ j ∈ range (ℓ + 1), (ℓ.choose j : ℂ) *
          (∑ m ∈ range (j + 1), (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond j m : ℂ) *
            hypersequence a (m + 1) n) * ((n : ℂ) + 1) ^ (ℓ - j)

/-- Proposition 1: (i) (Boyadzhiev)
`p_{ℓ,m}(x, y) = ∑_{j=m}^{ℓ} C(ℓ, j) (-1)^m m! S(j, m) x^j y^{ℓ-j}`; (ii) (Katsuura)
`p_{ℓ,m}(x, y) = 0` for `ℓ < m` and `p_{m,m}(x, y) = (-1)^m x^m m!`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 1 (`integers-2024-A70-prop-1`). -/
public theorem_wanted alternatingBinomialPowerSum_eq_sum_stirlingSecond (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x y =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * (-1) ^ m * (m.factorial : ℂ) *
          (Nat.stirlingSecond j m : ℂ) * x ^ j * y ^ (ℓ - j) ∧
      (ℓ < m → alternatingBinomialPowerSum ℓ m x y = 0) ∧
      alternatingBinomialPowerSum m m x y = (-1) ^ m * x ^ m * (m.factorial : ℂ)

/-- Proposition 2 (i)–(iv): (i) `p_{ℓ,m}(x, x) = (-1)^m m! S(ℓ + 1, m + 1) x^ℓ`, in particular
`c_{ℓ,m}(0) = (-1)^m m! S(ℓ + 1, m + 1)`; (ii) `p_{ℓ,m}(0, y) = 0^m y^ℓ`; (iii)
`p_{ℓ,m}(x, 0) = (-1)^m m! S(ℓ, m) x^ℓ`, in particular
`∑_{k=0}^{m} (-1)^k C(m, k) k^{m+1} = (-1)^m m! C(m + 1, 2)`; (iv)
`p_{ℓ,m}(-1, m) = m! S(ℓ, m)`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 2 (i)–(iv) (`integers-2024-A70-prop-2`). -/
public theorem_wanted alternatingBinomialPowerSum_special_values (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ m x x =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m 1 1 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond (ℓ + 1) (m + 1) : ℂ) ∧
      alternatingBinomialPowerSum ℓ m 0 y = 0 ^ m * y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ m x 0 =
        (-1) ^ m * (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum (m + 1) m 1 0 =
        (-1) ^ m * (m.factorial : ℂ) * ((m + 1).choose 2 : ℂ) ∧
      alternatingBinomialPowerSum ℓ m (-1) m = (m.factorial : ℂ) * (Nat.stirlingSecond ℓ m : ℂ)

/-- Proposition 3: (i) `p_{ℓ,0} = y^ℓ`; (ii) `p_{ℓ,1} = y^ℓ - (x + y)^ℓ`; (iii)
`p_{ℓ,2} = y^ℓ - 2(x + y)^ℓ + (2x + y)^ℓ`; (iv) for `ℓ ≥ 1`,
`p_{ℓ,ℓ-1} = (-1)^{ℓ-1} ℓ! x^{ℓ-1} (y + (ℓ - 1)/2 · x)`; (v) `p_{ℓ,ℓ} = (-1)^ℓ ℓ! x^ℓ`;
(vi) `p_{0,m} = 0^m`; (vii) `∑_{m=0}^{ℓ} p_{ℓ,m}(x, y) = (y - x)^ℓ`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 3 (`integers-2024-A70-prop-3`). -/
public theorem_wanted alternatingBinomialPowerSum_small_cases (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ 0 x y = y ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 1 x y = y ^ ℓ - (x + y) ^ ℓ ∧
      alternatingBinomialPowerSum ℓ 2 x y = y ^ ℓ - 2 * (x + y) ^ ℓ + (2 * x + y) ^ ℓ ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ (ℓ - 1) x y =
        (-1) ^ (ℓ - 1) * (ℓ.factorial : ℂ) * x ^ (ℓ - 1) * (y + ((ℓ : ℂ) - 1) / 2 * x)) ∧
      alternatingBinomialPowerSum ℓ ℓ x y = (-1) ^ ℓ * (ℓ.factorial : ℂ) * x ^ ℓ ∧
      alternatingBinomialPowerSum 0 m x y = 0 ^ m ∧
      ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m x y = (y - x) ^ ℓ

/-- Proposition 4: (i) `p_{ℓ,m+1}(x, y) = p_{ℓ,m}(x, y) - p_{ℓ,m}(x, x + y)`; (ii)
`p_{ℓ,m}(x, x + y) = ∑_{j=m}^{ℓ} C(ℓ, j) p_{j,m}(x, y) x^{ℓ-j}`; (iii)
`p_{ℓ,m+1}(x, y) = -∑_{j=m}^{ℓ-1} C(ℓ, j) p_{j,m}(x, y) x^{ℓ-j}`; (iv)
`p_{ℓ+1,m}(x, y) = y p_{ℓ,m}(x, y) - m x p_{ℓ,m-1}(x, x + y)`; (v)
`p_{ℓ+1,m+1}(x, y) = ((m + 1) x + y) p_{ℓ,m+1}(x, y) - (m + 1) x p_{ℓ,m}(x, y)`; (vi) for
`ℓ ≥ 1`, `∂_y p_{ℓ,m}(x, y) = ℓ p_{ℓ-1,m}(x, y)`; (vii) for `ℓ ≥ 1`,
`p_{ℓ,m}(x, y) = (m x + y) p_{ℓ-1,m}(x, y) - m x p_{ℓ-1,m-1}(x, y)`. The initial values
`p_{ℓ,0} = y^ℓ`, `p_{0,m} = 0^m`, `p_{0,0} = 1` repeat Proposition 3 and are omitted.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Proposition 4 (`integers-2024-A70-prop-4`). -/
public theorem_wanted alternatingBinomialPowerSum_recurrences (x y : ℂ) (ℓ m : ℕ) :
    alternatingBinomialPowerSum ℓ (m + 1) x y =
        alternatingBinomialPowerSum ℓ m x y - alternatingBinomialPowerSum ℓ m x (x + y) ∧
      alternatingBinomialPowerSum ℓ m x (x + y) =
        ∑ j ∈ Icc m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum ℓ (m + 1) x y =
        -∑ j ∈ Ico m ℓ, (ℓ.choose j : ℂ) * alternatingBinomialPowerSum j m x y * x ^ (ℓ - j) ∧
      alternatingBinomialPowerSum (ℓ + 1) m x y =
        y * alternatingBinomialPowerSum ℓ m x y -
          m * x * alternatingBinomialPowerSum ℓ (m - 1) x (x + y) ∧
      alternatingBinomialPowerSum (ℓ + 1) (m + 1) x y =
        ((m + 1) * x + y) * alternatingBinomialPowerSum ℓ (m + 1) x y -
          (m + 1) * x * alternatingBinomialPowerSum ℓ m x y ∧
      (1 ≤ ℓ → deriv (fun z => alternatingBinomialPowerSum ℓ m x z) y =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m x y) ∧
      (1 ≤ ℓ → alternatingBinomialPowerSum ℓ m x y =
        (m * x + y) * alternatingBinomialPowerSum (ℓ - 1) m x y -
          m * x * alternatingBinomialPowerSum (ℓ - 1) (m - 1) x y)

/-- Corollary 4: for `ℓ, m ≥ 1`, `d/dn c_{ℓ,m}(n) = ℓ c_{ℓ-1,m}(n)` and
`c_{ℓ,m}(n) = (m + n + 1) c_{ℓ-1,m}(n) - m c_{ℓ-1,m-1}(n)`, with `c_{ℓ,m}(n) = p_{ℓ,m}(1, n + 1)`
for a complex variable `n` (the paper differentiates in `n`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 4, Equation (3.38) (`integers-2024-A70-cor-4`). -/
public theorem_wanted carlitzSum_deriv_and_recurrence {ℓ m : ℕ} (hℓ : 1 ≤ ℓ) (hm : 1 ≤ m)
    (n : ℂ) :
    deriv (fun z => alternatingBinomialPowerSum ℓ m 1 (z + 1)) n =
        ℓ * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) ∧
      alternatingBinomialPowerSum ℓ m 1 (n + 1) =
        (m + n + 1) * alternatingBinomialPowerSum (ℓ - 1) m 1 (n + 1) -
          m * alternatingBinomialPowerSum (ℓ - 1) (m - 1) 1 (n + 1)

/-- Corollary 5: `∑_{k=1}^{n} k^m = ∑_{k=0}^{m} (-1)^{m-k} k! C(n + k, k + 1) S(m, k)`.
The paper takes `n ≥ 1`; `n = 0` also holds (both sides vanish) and is included.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Corollary 5, Equation (4.4) (`integers-2024-A70-cor-5`). -/
public theorem_wanted sum_pow_eq_sum_stirlingSecond (n m : ℕ) :
    ∑ k ∈ Icc 1 n, (k : ℤ) ^ m =
      ∑ k ∈ range (m + 1),
        (-1) ^ (m - k) * (k.factorial : ℤ) * ((n + k).choose (k + 1) : ℤ) *
          (Nat.stirlingSecond m k : ℤ)

/-- Lemma 1: `C(n + m - k - 1, m) = ∑_{j=0}^{k} (-1)^j C(k, j) C(n + m - j - 1, m - j)`, with
generalized binomial coefficients (upper argument in `ℤ` via `Ring.choose`; `C(x, i) = 0` for
`i < 0`).

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 1, Equation (4.10) (`integers-2024-A70-lem-1`). -/
public theorem_wanted ringChoose_sub_eq_sum (m n k : ℕ) :
    Ring.choose ((n : ℤ) + m - k - 1) m =
      ∑ j ∈ range (k + 1), (-1) ^ j * (k.choose j : ℤ) *
        (if j ≤ m then Ring.choose ((n : ℤ) + m - j - 1) (m - j) else 0)

/-- Lemma 2: `(k + 1)^ℓ = ∑_{j=0}^{k} C(k, j) j! S(ℓ + 1, j + 1)`.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Lemma 2, Equation (4.11) (`integers-2024-A70-lem-2`). -/
public theorem_wanted succ_pow_eq_sum_stirlingSecond (k ℓ : ℕ) :
    (k + 1) ^ ℓ = ∑ j ∈ range (k + 1), k.choose j * j.factorial * Nat.stirlingSecond (ℓ + 1) (j + 1)

/-- Theorem 10: `∑_{k=0}^{n} k^ℓ F_k = ∑_{m=0}^{ℓ} c_{ℓ,m}(n) F_{n+2(m+1)} -
∑_{m=0}^{ℓ} c_{ℓ,m}(0) F_{2(m+1)}`. The conjecture on the constant term that follows in the
record is omitted.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 10, Equation (4.7) (`integers-2024-A70-thm-10`). -/
public theorem_wanted sum_pow_mul_fib_eq (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * Nat.fib k =
      ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 (n + 1) * Nat.fib (n + 2 * (m + 1)) -
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 1 * Nat.fib (2 * (m + 1))

/-- Theorem 11: `∑_{k=0}^{n} k^ℓ L_k = ∑_{m=0}^{ℓ} c_{ℓ,m}(n) L_{n+2(m+1)} -
∑_{m=0}^{ℓ} c_{ℓ,m}(0) L_{2(m+1)} + L_0 · 0^ℓ`. The conjecture on the constant term that follows
in the record is omitted.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 11, Equation (4.9) (`integers-2024-A70-thm-11`). -/
public theorem_wanted sum_pow_mul_lucas_eq (ℓ n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) ^ ℓ * lucasNumber k =
      ∑ m ∈ range (ℓ + 1),
          alternatingBinomialPowerSum ℓ m 1 (n + 1) * lucasNumber (n + 2 * (m + 1)) -
        ∑ m ∈ range (ℓ + 1), alternatingBinomialPowerSum ℓ m 1 1 * lucasNumber (2 * (m + 1)) +
        lucasNumber 0 * 0 ^ ℓ

end

end MetaMathlibExt
