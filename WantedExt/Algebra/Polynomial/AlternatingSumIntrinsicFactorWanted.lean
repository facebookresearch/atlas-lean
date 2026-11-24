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
public import MathlibExt.Algebra.Polynomial.AlternatingSumIntrinsicFactor

/-!
# The factor `(x - 1)^n` for polynomials with distinct real roots (statement)

This statement is from Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving
Certain Rational Functions*, INTEGERS 26 (2026), Article A9. The case `f = x + a` is proved in
`MathlibExt.Algebra.Polynomial.AlternatingSumIntrinsicFactor` and re-exported here.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

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
