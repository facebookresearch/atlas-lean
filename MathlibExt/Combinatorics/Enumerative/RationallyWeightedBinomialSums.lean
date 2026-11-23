/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import MathlibExt.NumberTheory.DilcherFiniteMultipleHarmonic

/-!
# Rationally weighted binomial sums

For every natural number `n`, `∑_{k=0}^n binom(n, k) / (k + 1) = (2^{n+1} - 1) / (n + 1)` in `ℚ`
(`MetaMathlibExt.sum_choose_div_succ`).

The alternating binomial sum with inverse-square weights equals the sum of the harmonic
numbers divided by their indices. This follows from Dilcher's identity at exponent two by
grouping the weakly increasing pairs by their second entry.

## Proof of Epsteen's identity

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

/-- **Alternating binomial sum with inverse-square weights.** For every natural number $n$, with
$H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k^2} \binom{n}{k} = \sum_{k=1}^{n} \frac{H_k}{k}.$$

This is the case $x = -1$ of identity (3.6) of the source.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_neg_one_pow_choose_div_sq_eq_sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, harmonic k / k := by
  classical
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  let pairWeight (i j : ℕ) : ℚ := if i ≤ j then (↑(i + 1) : ℚ)⁻¹ / ↑(j + 1) else 0
  have inner (j : Fin n) :
      (∑ i : Fin n, pairWeight i j) = harmonic (j.val + 1) / ↑(j.val + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => pairWeight i j), harmonic, Finset.sum_div]
    simp only [pairWeight, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ js ∈ Finset.univ.filter (fun js : Fin 2 → Fin n => Monotone (fun i => (js i).val)),
          (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
      simpa only [mul_comm] using dilcher_finite_multiple_harmonic_identity_general 2 n hn
    _ = ∑ p : Fin n × Fin n, pairWeight p.1 p.2 := by
      rw [Finset.sum_filter]
      refine Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ fun js => ?_
      simp [pairWeight, Fin.monotone_iff_le_succ, Fin.forall_fin_one, Fin.prod_univ_two,
        finTwoArrowEquiv_apply, div_eq_mul_inv, mul_comm]
    _ = ∑ j : Fin n, harmonic (j.val + 1) / ↑(j.val + 1) := by
      rw [Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun j _ => inner j
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => harmonic (j + 1) / ↑(j + 1)),
        ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

end MetaMathlibExt
