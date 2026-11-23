/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Epsteen's identity

For every natural number `n`, `∑_{k=0}^n binom(n, k) / (k + 1) = (2^{n+1} - 1) / (n + 1)` in `ℚ`
(`MetaMathlibExt.sum_choose_div_succ`).

## Proof outline

The absorption identity `(n + 1) binom(n, k) = binom(n + 1, k + 1) (k + 1)`
(`Nat.add_one_mul_choose_eq`) turns each term into `binom(n + 1, k + 1) / (n + 1)`. The remaining
sum `∑_{k=0}^n binom(n + 1, k + 1)` is the row sum `∑_{j=0}^{n+1} binom(n + 1, j) = 2^{n+1}`
(`Nat.sum_range_choose`) without its term `binom(n + 1, 0) = 1`.

## Implementation notes

`sum_choose_div_succ` keeps the full name and the statement it had as a wanted theorem in
`WantedExt.Combinatorics.Enumerative.RationallyWeightedBinomialSumsWanted`.
-/

namespace MetaMathlibExt

/-- **Epsteen's identity.** For every natural number $n$,

$$\sum_{k=0}^{n} \frac{1}{k+1} \binom{n}{k} = \frac{2^{n+1} - 1}{n+1}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_choose_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1) := by
  -- Absorption: each term is `binom(n + 1, k + 1) / (n + 1)`.
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) / (k + 1) = ((n + 1).choose (k + 1) : ℚ) / (n + 1) := by
    intro k _
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have h : ((n : ℚ) + 1) * n.choose k = (n + 1).choose (k + 1) * ((k : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    linarith
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  -- Row `n + 1` of Pascal's triangle sums to `2 ^ (n + 1)`; drop its first entry `1`.
  have hrow := Nat.sum_range_choose (n + 1)
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at hrow
  have hrow' : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℚ)) + 1 = 2 ^ (n + 1) := by
    exact_mod_cast hrow
  linarith

end MetaMathlibExt
