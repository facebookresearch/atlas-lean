/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.BalancingRepdigit

namespace MetaMathlibExt

@[expose] public section

/-- **Balancing numbers that are concatenations of two repdigits.** For every natural number $k$,
if the balancing number $B_k$ is a concatenation of two repdigits, then $B_k = 35$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 3 (`integers-2025-A15-lem-3`). -/
public theorem_wanted balancingNum_concatTwoRepdigits (k : ℕ)
    (h : IsConcatTwoRepdigits (balancingNum k).toNat) :
    balancingNum k = 35

/-- **Balancing numbers that are concatenations of three repdigits.** For every natural number
$k$, if the balancing number $B_k$ is a concatenation of three repdigits, then $B_k = 204$ or
$B_k = 1189$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 4 (`integers-2025-A15-lem-4`). -/
public theorem_wanted balancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (balancingNum k).toNat) :
    balancingNum k = 204 ∨ balancingNum k = 1189

/-- **Lucas-balancing numbers that are concatenations of three repdigits.** For every natural
number $k$, if the decimal expansion of the Lucas-balancing number $C_k$ consists of exactly
three runs of equal digits, that is, $C_k$ is three blocks of repeated digits in which adjacent
blocks have different digits, then $C_k = 3363$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Lemma 6 (`integers-2025-A15-lem-6`). -/
public theorem_wanted lucasBalancingNum_concatThreeRepdigits (k : ℕ)
    (h : IsConcatThreeRepdigits (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3363

/-- **Balancing numbers that are differences of two repdigits.** Let $k \ge 2$ be a natural
number. If the balancing number $B_k$ is a difference of two repdigits, then $B_k = 6$ or
$B_k = 35$.

The hypothesis $k \ge 2$ excludes $B_0 = 0 = 1 - 1$ and $B_1 = 1 = 2 - 1$, which are also
differences of two repdigits.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 2 (`integers-2025-A15-thm-2`). -/
public theorem_wanted balancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (balancingNum k).toNat) :
    balancingNum k = 6 ∨ balancingNum k = 35

/-- **Lucas-balancing numbers that are differences of two repdigits.** For every natural
number $k \ge 2$, if the Lucas-balancing number $C_k$ is a difference of two repdigits, then
$C_k = 3$ or $C_k = 17$.

Both values occur: $C_2 = 3 = 11 - 8$ and $C_3 = 17 = 22 - 5$. The hypothesis $k \ge 2$ excludes
$C_1 = 1 = 2 - 1$.

Source: Mohapatra, Bhoi and Panda, *Balancing and Lucas-Balancing Numbers as the Difference of Two
Repdigits*, INTEGERS 25 (2025), Article A15, Theorem 3 (`integers-2025-A15-thm-3`). -/
public theorem_wanted lucasBalancingNum_repdigitDiff (k : ℕ) (hk : 2 ≤ k)
    (h : IsRepdigitDiff (lucasBalancingNum k).toNat) :
    lucasBalancingNum k = 3 ∨ lucasBalancingNum k = 17

end

end MetaMathlibExt
