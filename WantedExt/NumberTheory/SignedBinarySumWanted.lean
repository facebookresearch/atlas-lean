/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Signed power-of-two sums.** For natural numbers $m$, $s$ and $t$, an integer $n$ is a signed
power-of-two sum with coefficients in $\{-1, m\}$ over the range $s \le j \le t$ if
$n = \sum_{j=s}^{t} \lambda_j 2^j$ for some integers $\lambda_j$ with every
$\lambda_j \in \{-1, m\}$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7. -/
public def IsSignedPowTwoSum (m s t : ℕ) (n : ℤ) : Prop :=
  ∃ lam : ℕ → ℤ, (∀ j ∈ Finset.Icc s t, lam j = -1 ∨ lam j = (m : ℤ)) ∧
    n = ∑ j ∈ Finset.Icc s t, lam j * 2 ^ j

/-- **Example of a signed power-of-two sum.** The integer $1$ can be written as
$\sum_{j=0}^{1} \lambda_j 2^j$ with every $\lambda_j \in \{-1, 3\}$, namely
$1 = 3 \cdot 2^0 + (-1) \cdot 2^1$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7. -/
public theorem isSignedPowTwoSum_one : IsSignedPowTwoSum 3 0 1 1 := by
  refine ⟨fun j => if j = 0 then 3 else -1, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_Icc] at hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp
  · have hIcc : Finset.Icc 0 1 = {0, 1} := by decide
    rw [hIcc]
    simp

/-- **Interval and congruence characterization of signed power-of-two sums.** Let $m \ge 1$ and
$s \le t$ be natural numbers and put $L = t - s + 1$. An integer $n$ can be written as
$\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$ if and only if
$-2^s (2^L - 1) \le n \le 2^s m (2^L - 1)$ and $n \equiv -2^s (2^L - 1) \pmod{2^s (m + 1)}$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and
`m ≥ 1`, the integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with
`λⱼ ∈ {-1, m}` are precisely the integers `n` in the interval
`[-2^s * (2^{t-s+1} - 1), 2^s * m * (2^{t-s+1} - 1)]` satisfying
`n ≡ -2^s * (2^{t-s+1} - 1) [ZMOD 2^s * (m + 1)]`. -/
public theorem_wanted isSignedPowTwoSum_iff (m s t : ℕ) (hm : 1 ≤ m)
    (hst : s ≤ t) (n : ℤ) :
    IsSignedPowTwoSum m s t n ↔
      -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) ≤ n ∧
      n ≤ 2 ^ s * (m : ℤ) * (2 ^ (t - s + 1) - 1) ∧
      n ≡ -(2 : ℤ) ^ s * (2 ^ (t - s + 1) - 1) [ZMOD 2 ^ s * ((m : ℤ) + 1)]

/-- **Extending a signed power-of-two sum to a longer range.** Let $m \ge 1$, $s$, $t$ and $\alpha$
be natural numbers, let $\beta = \nu_2(m + 1)$ be the exponent of $2$ in $m + 1$, and suppose that
$s + \beta \le t + 1$ and $2^\alpha \equiv 1 \pmod{(m + 1)/2^\beta}$. If an integer $n$ can be
written as $\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$, then $n$ can also be
written as $\sum_{j=s}^{t+\alpha} \mu_j 2^j$ with every $\mu_j \in \{-1, m\}$.

The source's hypothesis $t \ge s + \beta - 1$ is written as $s + \beta \le t + 1$ to cover the
case $\beta = 0$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let
`β = ν₂(m + 1)`. If `n` is a signed power-of-two sum over `[s, t]` with
`t ≥ s + β - 1`, then `n` is also expressible over `[s, t + α]` whenever
`2^α ≡ 1 [(m + 1) / 2^β]`. -/
public theorem_wanted isSignedPowTwoSum_extend (m s t α : ℕ) (hm : 1 ≤ m)
    (hβ : s + (m + 1).factorization 2 ≤ t + 1)
    (hα : 2 ^ α ≡ 1 [ZMOD ((m + 1) / 2 ^ ((m + 1).factorization 2) : ℤ)])
    (n : ℤ) (h : IsSignedPowTwoSum m s t n) :
    IsSignedPowTwoSum m s (t + α) n

/-- **Integers that are one plus a signed sum of powers of two.** An integer $n$ can be written as
$n = 1 + \sum_{j=1}^{k} \lambda_j 2^j$ for some $k \ge 1$ and some
$\lambda_1, \dots, \lambda_k \in \{-1, 1\}$ if and only if $n \equiv 3 \pmod 4$.

Source: Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 12 (`jis-2024-24.7.5-lem-12`): an integer `n` can be
written as `1 + ∑_{j=1}^{k} λⱼ * 2^j` for some `k ≥ 1` and coefficients
`λⱼ ∈ {-1, 1}` if and only if `n ≡ 3 [ZMOD 4]`. -/
public theorem_wanted one_add_signedPowTwoSum_iff (n : ℤ) :
    (∃ k : ℕ, 1 ≤ k ∧ ∃ lam : ℕ → ℤ,
      (∀ j ∈ Finset.Icc 1 k, lam j = -1 ∨ lam j = 1) ∧
      n = 1 + ∑ j ∈ Finset.Icc 1 k, lam j * 2 ^ j) ↔ n ≡ 3 [ZMOD 4]

end

end MetaMathlibExt
