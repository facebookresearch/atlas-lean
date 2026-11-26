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

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **The constant in Mertens' first theorem.** With $p$ ranging over the primes and $\log$ the
natural logarithm, this is the real number
$$M = \lim_{n \to \infty} \Bigl(\sum_{p \le n} \frac{\log p}{p} - \log n\Bigr),$$
the limit taken over natural numbers $n$. -/
noncomputable def mertensConstant : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ =>
    (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      Real.log p / (p : ℝ)) - Real.log n)

/-- **Dusart's explicit Mertens first theorem.** Let $p$ range over the primes, let $\log$ be the
natural logarithm, and let
$M = \lim_{n \to \infty} \bigl(\sum_{p \le n} \frac{\log p}{p} - \log n\bigr)$ be the constant in
Mertens' first theorem. For every real number $x \ge 912560$ there is a real number $E$ with
$|E| \le \frac{0.3}{(\log x)^2}$ such that
$$\sum_{p \le x} \frac{\log p}{p} = \log x + M + E.$$

Source: Pierre Dusart, *Explicit estimates of some functions over primes*,
Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.7. -/
theorem_wanted dusart_log_prime_sum (x : ℝ) (hx : 912560 ≤ x) :
    ∃ E, ((∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1)),
        Real.log p / (p : ℝ))
      = Real.log x + mertensConstant + E
      ∧ |E| ≤ 0.3 / (Real.log x) ^ 2)

end

end MetaMathlibExt
