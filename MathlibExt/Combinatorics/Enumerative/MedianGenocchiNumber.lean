/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Median Genocchi numbers

The definitions follow Kwang-Wu Chen, *An Interesting Lemma for Regular
C-fractions*, Journal of Integer Sequences 13 (2010), Article 10.5.3.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Genocchi numbers via Bernoulli numbers.** For a natural number $n$, the Genocchi number $G_n$
is the rational number $G_n = 2(1 - 2^n) B_n$, where $B_n$ is the $n$-th Bernoulli number with the
convention $B_1 = -\tfrac{1}{2}$. -/
def genocchiNumberViaBernoulli (n : ℕ) : ℚ :=
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n

/-- **Odd-indexed median Genocchi numbers.** For a natural number $m$, let $B_m$ be the $m$-th
Bernoulli number and $G_m = 2(1 - 2^m) B_m$ the $m$-th Genocchi number. For a natural number $n$,
the median Genocchi number $H_{2n+1}$ is the rational number defined by $H_1 = 1$ and, for
$n \ge 1$,
$$H_{2n+1} = \sum_{k=0}^{\lfloor (n-1)/2 \rfloor} \binom{n}{2k+1} G_{2n-2k}.$$

These values carry signs: $H_3 = -1$ and $H_5 = 2$.

Source: concept `jis_sem_7cda4ff413e183d46cd0c8e9`; statements `jis_94b979a01da48153660bbf5f`
and `jis_41a43df0c7633bde6c183242`.
-/
def medianGenocchiOdd (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ∑ k ∈ Finset.range ((n - 1) / 2 + 1),
    (Nat.choose n (2 * k + 1) : ℚ) * genocchiNumberViaBernoulli (2 * n - 2 * k)

@[simp]
theorem medianGenocchiOdd_zero : medianGenocchiOdd 0 = 1 := by
  simp [medianGenocchiOdd]

@[simp]
theorem medianGenocchiOdd_one : medianGenocchiOdd 1 = -1 := by
  have h : genocchiNumberViaBernoulli 2 = -1 := by
    rw [genocchiNumberViaBernoulli, bernoulli_two]
    norm_num
  simp [medianGenocchiOdd, h]

end

end MetaMathlibExt
