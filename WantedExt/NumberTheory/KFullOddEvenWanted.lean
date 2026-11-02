/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.KFull
public import MathlibExt.NumberTheory.PowerFree

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- **Odd-to-even ratio of $k$-full numbers.** Let $k \ge 2$. For a natural number $N$ let
$K_o(N)$ and $K_e(N)$ be the numbers of odd and of even $k$-full numbers $n \le N$. Then
$K_o(N)/K_e(N) \to 2 - 2^{1 - 1/k}$ as $N \to \infty$.

The counts up to a real $x$ depend only on $\lfloor x \rfloor$, so this is the same as the limit
as $x \to \infty$ through the reals.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Corollary 2
(`integers-2024-A106-cor-2`). -/
public theorem_wanted tendsto_card_odd_kFull_div_card_even_kFull {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Even n}.ncard)
      atTop (𝓝 (2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ))))

/-- **Odd-to-even ratio of $k$-full, $l$-free numbers.** Let $2 \le k < l$. Call a natural number
$n$ a $[k, l]$-integer if it is $k$-full and $l$-free, that is, $n \ge 1$ and every prime $p$
dividing $n$ satisfies $p^k \mid n$ and $p^l \nmid n$. For a natural number $N$ let $O_{k,l}(N)$
and $E_{k,l}(N)$ be the numbers of odd and of even $[k, l]$-integers $n \le N$. Then
$O_{k,l}(N)/E_{k,l}(N) \to (2 - 2^{1 - 1/k})/(1 - 2^{1 - l/k})$ as $N \to \infty$.

The counts up to a real $x$ depend only on $\lfloor x \rfloor$, so this is the same as the limit
as $x \to \infty$ through the reals.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Theorem 1
(`integers-2024-A106-thm-1`). -/
public theorem_wanted tendsto_card_odd_kFull_lFree_div_card_even_kFull_lFree {k l : ℕ}
    (hk : 2 ≤ k) (hkl : k < l) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧
            Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ n.IsPowerFree l ∧
            Even n}.ncard)
      atTop (𝓝 ((2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ))) / (1 - (2 : ℝ) ^ (1 - (l : ℝ) / k))))

/-- **Odd-to-even ratio of $l$-free numbers.** Let $l \ge 2$. For a natural number $N$ let $O(N)$
and $E(N)$ be the numbers of odd and of even $l$-free positive integers $n \le N$. Then
$O(N)/E(N) \to 2^l/(2^l - 2)$ as $N \to \infty$.

This is the case $k = 1$ of the odd-to-even ratio for $k$-full, $l$-free numbers, since every
positive integer is $1$-full.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Corollary 1
(`integers-2024-A106-cor-1`). -/
public theorem_wanted tendsto_card_odd_lFree_div_card_even_lFree {l : ℕ} (hl : 2 ≤ l) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧
            Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧
            Even n}.ncard)
      atTop (𝓝 ((2 : ℝ) ^ l / ((2 : ℝ) ^ l - 2)))

end

end MetaMathlibExt
