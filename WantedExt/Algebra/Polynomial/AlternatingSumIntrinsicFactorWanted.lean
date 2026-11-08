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

/-- Theorem 1.1: for every real `a` and `n ≥ 0`, `(x - 1)^n` divides
`H_n(x; a) = ∑_{i=0}^n (-1)^i C(n, i) ∏_{k=0, k ≠ i}^n (x^k + a)`, a formal cross-multiplied
polynomial; for `a ≠ -1` (the paper's condition) it is the numerator of
`G_n(x; a) = ∑_{i=0}^n (-1)^i C(n, i) / (x^i + a)`, while at `a = -1` the factor `x^0 + a` is
zero and only the polynomial statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 1.1 (`integers-2026-A9-thm-1-1`). -/
public theorem_wanted X_sub_one_pow_dvd_alternating_sum_prod_X_pow_add_C (n : ℕ) (a : ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (X ^ k + C a)

/-- Theorem 3.1: for `f = c ∏_{r ∈ s} (x - r)` with distinct real roots `r ∈ s`, `(x - 1)^n`
divides the formal cross-multiplied polynomial
`∑_{i=0}^n (-1)^i C(n, i) ∏_{k=0, k ≠ i}^n f(x^k)`.
Under the paper's conditions `c ≠ 0`, `1 ∉ s` it is the numerator of
`Q_n(x; f) = ∑_{i=0}^n (-1)^i C(n, i) / f(x^i)`; for `c = 0` or `1 ∈ s` some `f(x^k)` is zero
and only the polynomial statement remains.

Source: Takashi Agoh, *An Intrinsic Factor of an Alternating Sum Involving Certain Rational
Functions*, INTEGERS 26 (2026), Article A9, Theorem 3.1 (`integers-2026-A9-thm-3-1`). -/
public theorem_wanted X_sub_one_pow_dvd_alternating_sum_prod_comp_X_pow (n : ℕ) (c : ℝ)
    (s : Finset ℝ) :
    (X - 1 : ℝ[X]) ^ n ∣ ∑ i ∈ Finset.range (n + 1),
      (-1 : ℝ[X]) ^ i * (n.choose i : ℝ[X]) *
        ∏ k ∈ (Finset.range (n + 1)).erase i, (C c * ∏ r ∈ s, (X - C r)).comp (X ^ k)

end

end MetaMathlibExt
