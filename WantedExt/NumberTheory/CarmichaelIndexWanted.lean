/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.NumberTheory.CarmichaelIndex

/-!
# Carmichael indices

Yamagami and Inaba's product formula expresses the Carmichael index `N(n)` in terms of the
prime powers dividing `n`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Product formula for the Carmichael index.** Let $n \ge 2$ and, for each prime $p$ dividing
$n$, let $p^{e_p}$ be the largest power of $p$ dividing $n$. Then the Carmichael index of $n$ is
$N(n) = \prod_p \bigl(N(n; p^{e_p}) + 1\bigr)$, the product running over the primes $p$ dividing
$n$, where $N(n; p^{e_p})$ is the number of units of $\mathbb{Z}/p^{e_p}\mathbb{Z}$ whose
multiplicative order divides $\gcd(p - 1, n/p^{e_p} - 1)$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 1 (`integers-2024-A40-thm-1`). -/
public theorem_wanted carmichaelIndex_eq_prod (n : ℕ) (hn : 2 ≤ n) :
    carmichaelIndex n = ∏ p ∈ n.primeFactors,
      (Nat.card {u : (ZMod (p ^ n.factorization p))ˣ //
        orderOf u ∣ Nat.gcd (p - 1) (n / p ^ n.factorization p - 1)} + 1)

end

end MetaMathlibExt
