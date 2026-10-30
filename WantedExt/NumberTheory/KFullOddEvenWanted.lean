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

/-- Corollary 2: for `k ≥ 2`, the number `K_o(x)` of odd `k`-full numbers up to `x`
and the number `K_e(x)` of even `k`-full numbers up to `x` satisfy
`K_o(x) / K_e(x) → 2 - 2^{1 - 1/k}` as `x → ∞`. `k`-full is the standard notion
(`Nat.IsKFull`: `n ≠ 0` and `p^k ∣ n` for every prime `p ∣ n`, so `1` is `k`-full);
both counts depend only on `⌊x⌋`, so the limit is taken along natural numbers `N`.
The paper's identification of these counts with its `O_{k,⌊x⌋}(x)` and
`E_{k,⌊x⌋}(x)` is not stated.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Corollary 2
(`integers-2024-A106-cor-2`). -/
public theorem_wanted tendsto_card_odd_kFull_div_card_even_kFull {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull k n ∧ Even n}.ncard)
      atTop (𝓝 (2 - (2 : ℝ) ^ (1 - 1 / (k : ℝ))))

/-- Theorem 1: for `2 ≤ k < l`, call `n` a `[k, l]`-integer if `n ≥ 1` and every prime
`p ∣ n` satisfies `p ^ k ∣ n` and `p ^ l ∤ n` (`k`-full and `l`-free; stated as `Nat.IsKFull k n`
and `n.IsPowerFree l`). The numbers
`O_{k,l}(x)` and `E_{k,l}(x)` of odd and even `[k, l]`-integers up to `x` satisfy
`O_{k,l}(x) / E_{k,l}(x) → (2 - 2^{1 - 1/k}) / (1 - 2^{1 - l/k})` as `x → ∞`. Both
counts depend only on `⌊x⌋`, so the limit is taken along natural numbers `N`.

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

/-- Corollary 1 (the case `k = 1` of Theorem 1): for `l ≥ 2`, the numbers `O_{1,l}(x)`
and `E_{1,l}(x)` of odd and even `l`-free positive integers up to `x` (`[1, l]`-integers:
`Nat.IsKFull 1 n` is `n ≠ 0`, `l`-free is `n.IsPowerFree l`) satisfy
`O_{1,l}(x) / E_{1,l}(x) → 2^l / (2^l - 2)`. The limit is taken along natural numbers `N`.

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
