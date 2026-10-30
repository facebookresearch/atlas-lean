/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import WantedExt.NumberTheory.GenLeonardoWanted

namespace MetaMathlibExt

@[expose] public section

/-- Log-concavity propagates along a positive linear recurrence with one
positive and `k - 1` subtracted nonnegative coefficients: if a positive real
sequence satisfies `z n = c₁ z (n-1) - c₂ z (n-2) - ⋯ - c_k z (n-k)` for
`n ≥ k` (with `k ≥ 2` and `c_j ≥ 0` for `2 ≤ j ≤ k`) and its initial block
`z 0, …, z k` is log-concave (`z (i-1) z (i+1) ≤ z i ^ 2` for
`1 ≤ i < k`), then the whole sequence is log-concave. The paper assumes the
block `z 0, …, z (k+1)` is log-concave; its `i = k` inequality is dropped
because the recurrence at `n = k + 1` propagates it from the `i < k` ones. The
paper's hypothesis `c₁ > 0` is omitted: it follows from positivity and the
recurrence at `n = k`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1
(quoted from the paper's reference [17]) (`integers-2024-A82-lem-1`). -/
public theorem_wanted logConcave_of_linearRecurrence_of_initial_logConcave
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z (i - 1) * z (i + 1) ≤ z i ^ 2) :
    ∀ n, 1 ≤ n → z (n - 1) * z (n + 1) ≤ z n ^ 2

/-- Log-convexity propagates along a positive linear recurrence with one
positive and `k - 1` subtracted nonnegative coefficients: under the
recurrence of `logConcave_of_linearRecurrence_of_initial_logConcave`, if the
initial block `z 0, …, z k` is log-convex
(`z i ^ 2 ≤ z (i-1) z (i+1)` for `1 ≤ i < k`), then the whole sequence is
log-convex. The paper assumes the block `z 0, …, z (k+1)` is log-convex; its
`i = k` inequality is dropped because the recurrence propagates it. The
paper's hypothesis `c₁ > 0` is omitted: it follows from positivity and the
recurrence at `n = k`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 1,
log-convex reading (quoted from the paper's reference [17])
(`integers-2024-A82-lem-1`). -/
public theorem_wanted logConvex_of_linearRecurrence_of_initial_logConvex
    (k : ℕ) (hk : 2 ≤ k) (c : ℕ → ℝ) (hc : ∀ j, 2 ≤ j → j ≤ k → 0 ≤ c j)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, k ≤ n →
      z n = c 1 * z (n - 1) - ∑ j ∈ Finset.Icc 2 k, c j * z (n - j))
    (hinit : ∀ i, 1 ≤ i → i < k → z i ^ 2 ≤ z (i - 1) * z (i + 1)) :
    ∀ n, 1 ≤ n → z n ^ 2 ≤ z (n - 1) * z (n + 1)

/-- Log-balancedness of reciprocals along `z (n+1) = c₁ z n - c₂ z (n-2)`: let `z` be a positive
real sequence with `z (n+1) = c₁ z n - c₂ z (n-2)` for `n ≥ 2`, where `c₂ ≥ 0`, and let
`x n = z (n+1) / z n`. If the block `1/z n₀, …, 1/z (n₀+3)` is log-balanced and
`c₁ x n x (n+1) - 3 c₂ ≥ 0` for `n ≥ n₀`, then `(1/z n)_{n ≥ n₀}` is log-balanced. Log-balanced
is the standard notion (Došlić): `w` is log-convex (`w n ^ 2 ≤ w (n-1) w (n+1)`) and `w n / n!`
is log-concave, both at every interior index `n` (here `n ≥ n₀ + 1`; for the block, `n = n₀ + 1,
n₀ + 2`). The paper's hypothesis `c₁ > 0` is omitted: it follows from positivity, the recurrence
and `c₂ ≥ 0`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Lemma 2
(`integers-2024-A82-lem-2`). -/
public theorem_wanted inv_logBalanced_of_recurrence_of_initial (c₁ c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (z : ℕ → ℝ) (hpos : ∀ n, 0 < z n)
    (hrec : ∀ n, 2 ≤ n → z (n + 1) = c₁ * z n - c₂ * z (n - 2)) (n₀ : ℕ)
    (hinit : ∀ n, n₀ + 1 ≤ n → n ≤ n₀ + 2 →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2)
    (hx : ∀ n, n₀ ≤ n → 3 * c₂ ≤ c₁ * (z (n + 1) / z n) * (z (n + 2) / z (n + 1))) :
    ∀ n, n₀ + 1 ≤ n →
      (1 / z n) ^ 2 ≤ (1 / z (n - 1)) * (1 / z (n + 1)) ∧
        (1 / z (n - 1) / (n - 1).factorial) * (1 / z (n + 1) / (n + 1).factorial) ≤
          (1 / z n / n.factorial) ^ 2

/-- For every `k ≥ 1`, the reciprocals `(1/L_{k,n})_{n ≥ 3}` of the generalized Leonardo numbers
`L_{k,n} = MetaMathlibExt.genLeonardo k n` are log-balanced (standard notion, Došlić): for every
`n ≥ 4`, `(1/L_{k,n})² ≤ (1/L_{k,n-1}) (1/L_{k,n+1})` and
`(1/(L_{k,n-1} (n-1)!)) (1/(L_{k,n+1} (n+1)!)) ≤ (1/(L_{k,n} n!))²`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 1
(`integers-2024-A82-thm-1`). -/
public theorem_wanted inv_genLeonardo_logBalanced (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4 ≤ n) :
    (1 / (genLeonardo k n : ℝ)) ^ 2 ≤
        (1 / (genLeonardo k (n - 1) : ℝ)) * (1 / (genLeonardo k (n + 1) : ℝ)) ∧
      (1 / (genLeonardo k (n - 1) : ℝ) / (n - 1).factorial) *
          (1 / (genLeonardo k (n + 1) : ℝ) / (n + 1).factorial) ≤
        (1 / (genLeonardo k n : ℝ) / n.factorial) ^ 2

/-- For every `k ≥ 1`, the sequence `(L_{k,n}^{1/n})_{n ≥ 9}` of `n`-th roots of the generalized
Leonardo numbers is log-convex: `(L_{k,n}^{1/n})² ≤ L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}` for
every `n ≥ 10`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 3
(`integers-2024-A82-thm-3`). -/
public theorem_wanted genLeonardo_rpow_inv_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 10 ≤ n) :
    ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
      (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
        (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ))

/-- For every `k ≥ 1`, the partial sums `R_n = ∑_{i=0}^n L_{k,i}` of the generalized Leonardo
numbers satisfy `R_{n-1} R_{n+1} ≤ R_n²` for every `n ≥ 2`. The paper states this for every
`n ≥ 1`, but its own identity `R_n² - R_{n-1} R_{n+1} = (k+1)² (F_n + (-1)^n) + k(k+1)(n F_n -
2 F_{n+1}) + k²` gives `-k < 0` at `n = 1` (`R_0 = 1`, `R_1 = 2`, `R_2 = k + 4`), so the index
`n = 1` is excluded.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 2
(`integers-2024-A82-thm-2`). -/
public theorem_wanted genLeonardo_partialSum_logConcave (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 2 ≤ n) :
    (∑ i ∈ Finset.range n, genLeonardo k i) * (∑ i ∈ Finset.range (n + 2), genLeonardo k i) ≤
      (∑ i ∈ Finset.range (n + 1), genLeonardo k i) ^ 2

/-- For every `k ≥ 1` and every integer `n_k ≥ max {9, (1 + √(64k - 7))/4}`,
`(L_{k,n}^{1/n})_{n ≥ n_k}` is log-balanced (Došlić): for every `n ≥ n_k + 1`,
`(L_{k,n}^{1/n})² ≤ L_{k,n-1}^{1/(n-1)} L_{k,n+1}^{1/(n+1)}` and
`(L_{k,n-1}^{1/(n-1)} / (n-1)!) (L_{k,n+1}^{1/(n+1)} / (n+1)!) ≤ (L_{k,n}^{1/n} / n!)²`.
The paper says "there exists `n_k ≥ max {9, (1 + √(64k - 7))/4}`", which is no stronger than
"there exists `n_k`" since a tail of a log-balanced sequence is log-balanced; this states the
threshold its proof establishes (log-concavity of `L_{k,n}^{1/n}/n!` once
`n ≥ (1 + √(64k - 7))/4`, log-convexity of `L_{k,n}^{1/n}` from `n = 9`).

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 4
(`integers-2024-A82-thm-4`). -/
public theorem_wanted genLeonardo_rpow_inv_logBalanced (k : ℕ) (hk : 1 ≤ k) (nk : ℕ)
    (h9 : 9 ≤ nk) (hsqrt : (1 + Real.sqrt (64 * k - 7)) / 4 ≤ nk) :
    ∀ n : ℕ, nk + 1 ≤ n →
      ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n)) ^ 2 ≤
          (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) *
            (genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) ∧
        (genLeonardo k (n - 1) : ℝ) ^ ((1 : ℝ) / (n - 1 : ℕ)) / (n - 1).factorial *
            ((genLeonardo k (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1 : ℕ)) / (n + 1).factorial) ≤
          ((genLeonardo k n : ℝ) ^ ((1 : ℝ) / n) / n.factorial) ^ 2

/-- For every `k ≥ 1`, the sequence `(L_{k,n}^n)_{n ≥ 3}` is log-convex:
`L_{k,n}^{2n} ≤ L_{k,n-1}^{n-1} L_{k,n+1}^{n+1}` for every `n ≥ 4`.

Source: Feng-Zhen Zhao, *The Log-Behavior of Some Sequences Related to the
Generalized Leonardo Numbers*, INTEGERS 24 (2024), Article A82, Theorem 5
(`integers-2024-A82-thm-5`). -/
public theorem_wanted genLeonardo_pow_self_logConvex (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (hn : 4 ≤ n) :
    genLeonardo k n ^ (2 * n) ≤ genLeonardo k (n - 1) ^ (n - 1) * genLeonardo k (n + 1) ^ (n + 1)

end

end MetaMathlibExt
