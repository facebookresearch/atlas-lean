/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Real.Basic

/-!
# The factor `(x - 1)^n` of alternating binomial sums of rational functions (statements)

Statement-only targets from Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving
Certain Rational Functions*, INTEGERS 26 (2026), Article A9. For a polynomial `f`, the
statements use the formal cross-multiplied polynomial
`∑_{i=0}^n (-1)^i C(n, i) ∏_{k ≠ i} f(x^k)` (Equation (1.3) for `f = x + a`). When no
`f(x^k)` is the zero polynomial (the paper's nondegeneracy conditions, e.g. `a ≠ -1` for
`f = x + a`), it is the numerator of `∑_{i=0}^n (-1)^i C(n, i) / f(x^i)` over the common
denominator `∏_{k=0}^n f(x^k)`; the divisibility statements below are stated for the polynomial
itself and include the degenerate cases.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **The factor $(x - 1)^n$ of an alternating binomial sum.** For every real number $a$ and
every natural number $n$, the polynomial $(x - 1)^n$ divides, in $\mathbb{R}[x]$, the polynomial
$$H_n(x; a) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} \prod_{0 \le k \le n,\ k \ne i} (x^k + a).$$

For $a \ne -1$ (the paper's condition), $H_n(x; a)$ is the numerator of
$G_n(x; a) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} / (x^i + a)$ over the common denominator
$\prod_{k=0}^{n} (x^k + a)$; at $a = -1$ the factor $x^0 + a$ is zero and only the polynomial
statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 1.1 (`integers-2026-A9-thm-1-1`). -/
public theorem_wanted X_sub_one_pow_dvd_alternating_sum_prod_X_pow_add_C (n : ℕ) (a : ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (X ^ k + C a)

/-- **The factor $(x - 1)^n$ for polynomials with distinct real roots.** Let $c$ be a real
number, let $s$ be a finite set of real numbers, and let $f(x) = c \prod_{r \in s} (x - r)$ in
$\mathbb{R}[x]$. For every natural number $n$, the polynomial $(x - 1)^n$ divides the polynomial
$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} \prod_{0 \le k \le n,\ k \ne i} f(x^k).$$

For $c \ne 0$ and $1 \notin s$ (the paper's conditions), this polynomial is the numerator of
$Q_n(x; f) = \sum_{i=0}^{n} (-1)^i \binom{n}{i} / f(x^i)$ over the common denominator
$\prod_{k=0}^{n} f(x^k)$; for $c = 0$ or $1 \in s$ some $f(x^k)$ is zero and only the
polynomial statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 3.1 (`integers-2026-A9-thm-3-1`). -/
public theorem_wanted X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow (n : ℕ) (c : ℝ)
    (s : Finset ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (C c * ∏ r ∈ s, (X - C r)).comp (X ^ k)

end

end MetaMathlibExt
