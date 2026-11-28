/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter
public import MathlibExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumDefs

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Dusart's explicit Mertens second theorem.** Let $p$ range over the primes, let $\log$ be
the natural logarithm, and let
$B = \lim_{n \to \infty} \bigl(\sum_{p \le n} \frac{1}{p} - \log \log n\bigr)$ be the
Meissel–Mertens constant. For every real number $x \ge 2278383$ there is a real number $E$ with
$|E| \le \frac{0.2}{(\log x)^3}$ such that
$$\sum_{p \le x} \frac{1}{p} = \log \log x + B + E.$$

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.6. -/
theorem_wanted dusart_reciprocal_prime_sum (x : ℝ) (hx : 2278383 ≤ x) :
    ∃ E, ((∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)),
        1 / (p : ℝ))
      = Real.log (Real.log x) + meisselMertensConstant + E
      ∧ |E| ≤ 0.2 / (Real.log x) ^ 3)

end

end MetaMathlibExt
