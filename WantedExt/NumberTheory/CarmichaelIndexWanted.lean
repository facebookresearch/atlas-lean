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

/-!
# Carmichael indices

Wanted statements from Yamagami and Inaba on the Carmichael index `N(n)`, the number of
solutions of `xⁿ = x` in `ℤ/nℤ`. Korselt's criterion (the paper's Corollary 1) is already
`Nat.isCarmichael_iff_korselt` in Mathlib.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Carmichael index.** For a natural number $n$, the Carmichael index $N(n)$ is the number of
integers $a$ with $0 \le a \le n - 1$ and $a^n \equiv a \pmod{n}$.

Source: Atsushi Yamagami and Youichi Inaba, *On a Formula and Some Properties of Carmichael
Indices*, INTEGERS 24 (2024), Article A40, Definition 1. -/
public def carmichaelIndex (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun a => a ^ n ≡ a [MOD n]).card

/-- **The Carmichael index of 1.** The Carmichael index of $1$ is $N(1) = 1$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Section 1. -/
public theorem carmichaelIndex_one : carmichaelIndex 1 = 1 := by decide

/-- **The Carmichael indices of 4 and 66.** The Carmichael index satisfies $N(4) = 2$ and
$N(66) = 24$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Example 1 (Table 1) and Example 3. -/
public theorem carmichaelIndex_four_and_sixtySix :
    carmichaelIndex 4 = 2 ∧ carmichaelIndex 66 = 24 := by
  constructor <;> decide +kernel

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

/-- **The Carmichael index of $n$ is never $n - 1$.** For every positive integer $n$, the
Carmichael index $N(n)$, the number of integers $a$ with $0 \le a \le n - 1$ and
$a^n \equiv a \pmod{n}$, is not equal to $n - 1$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 2 (`integers-2024-A40-thm-2`). -/
public theorem_wanted carmichaelIndex_ne_sub_one (n : ℕ) (hn : 0 < n) :
    carmichaelIndex n ≠ n - 1

end

end MetaMathlibExt
