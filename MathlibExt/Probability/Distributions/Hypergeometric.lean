/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# The hypergeometric distribution

Draw `n` items without replacement from an urn of `N` items, `K` of which are marked. The
number of marked items drawn has the hypergeometric law
`h(k) = C(K, k) C(N - K, n - k) / C(N, n)` for `0 ≤ k ≤ n` (and `0` for `k > n`).

## Main definitions

* `ProbabilityTheory.hypergeometricReal N K n k`: the real-valued mass function `h(k)`.
* `ProbabilityTheory.hypergeometric N K n hK hn`: the hypergeometric law as a `PMF ℕ`.

## Main results

* `sum_hypergeometricReal`: `∑ k ≤ n, h(k) = 1` (Vandermonde's identity,
  `Nat.add_choose_eq`).
* `sum_mul_hypergeometricReal`: the mean is `n K / N` (for `N > 0`).

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
  Wiley (1968), §II.6.
-/

@[expose] public section

open Finset

namespace ProbabilityTheory

/-- The hypergeometric mass function: the probability `C(K, k) C(N - K, n - k) / C(N, n)` of
drawing exactly `k` marked items in `n` draws without replacement from `N` items of which `K`
are marked; it is `0` for `k > n`. The parameter domain is `K ≤ N`, `n ≤ N`; outside it the
value is not a probability (`N - K` truncates, and `C(N, n) = 0` makes it `0` for `n > N`). -/
noncomputable def hypergeometricReal (N K n k : ℕ) : ℝ :=
  if k ≤ n then (K.choose k * (N - K).choose (n - k) : ℝ) / N.choose n else 0

/-- The hypergeometric mass function is nonnegative. -/
theorem hypergeometricReal_nonneg (N K n k : ℕ) : 0 ≤ hypergeometricReal N K n k := by
  unfold hypergeometricReal
  split_ifs <;> positivity

/-- The hypergeometric mass function vanishes above the number of draws. -/
theorem hypergeometricReal_of_lt {N K n k : ℕ} (h : n < k) : hypergeometricReal N K n k = 0 := by
  simp [hypergeometricReal, not_le.2 h]

/-- The hypergeometric mass function vanishes above the number of marked items. -/
theorem hypergeometricReal_of_lt' {N K n k : ℕ} (h : K < k) :
    hypergeometricReal N K n k = 0 := by
  simp [hypergeometricReal, Nat.choose_eq_zero_of_lt h]

/-- Vandermonde's identity in the form `∑ₖ C(K, k) C(N - K, n - k) = C(N, n)`. -/
private lemma sum_choose_mul_choose {N K : ℕ} (hK : K ≤ N) (n : ℕ) :
    ∑ k ∈ range (n + 1), K.choose k * (N - K).choose (n - k) = N.choose n := by
  have h := Nat.add_choose_eq K (N - K) n
  rw [Nat.add_sub_cancel' hK, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => K.choose i * (N - K).choose j)] at h
  exact h.symm

/-- The first-moment identity `(∑ₖ k C(K, k) C(N - K, n - k)) N = n K C(N, n)`. -/
private lemma sum_mul_choose_mul_choose {N K : ℕ} (hK : K ≤ N) (n : ℕ) :
    (∑ k ∈ range (n + 1), k * (K.choose k * (N - K).choose (n - k))) * N =
      n * K * N.choose n := by
  rcases n with _ | n
  · simp
  rcases K with _ | K
  · rw [Finset.sum_eq_zero fun k _ => by rcases k with _ | k <;> simp]
    simp
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hterm : ∀ k ∈ range (n + 1), (k + 1) * ((K + 1).choose (k + 1) *
      (N + 1 - (K + 1)).choose (n + 1 - (k + 1))) =
      (K + 1) * (K.choose k * (N - K).choose (n - k)) := by
    intro k _
    rw [Nat.add_sub_add_right, Nat.add_sub_add_right, ← mul_assoc, mul_comm (k + 1),
      ← Nat.add_one_mul_choose_eq, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_choose_mul_choose (by omega : K ≤ N) n]
  have := Nat.add_one_mul_choose_eq N n
  rw [zero_mul, add_zero]
  calc (K + 1) * N.choose n * (N + 1) = (K + 1) * ((N + 1) * N.choose n) := by ring
    _ = (n + 1) * (K + 1) * (N + 1).choose (n + 1) := by rw [this]; ring

/-- **Normalization.** For `K ≤ N` and `n ≤ N` the hypergeometric probabilities sum to one;
this is Vandermonde's identity `∑ₖ C(K, k) C(N - K, n - k) = C(N, n)`. -/
theorem sum_hypergeometricReal {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) :
    ∑ k ∈ range (n + 1), hypergeometricReal N K n k = 1 := by
  have hpos : (0 : ℝ) < N.choose n := by exact_mod_cast Nat.choose_pos hn
  calc ∑ k ∈ range (n + 1), hypergeometricReal N K n k
      = (∑ k ∈ range (n + 1), (K.choose k * (N - K).choose (n - k) : ℝ)) / N.choose n := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hypergeometricReal, ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hk))]
    _ = 1 := by
        rw [div_eq_one_iff_eq hpos.ne']
        exact_mod_cast sum_choose_mul_choose hK n

/-- **Mean.** For `0 < N`, `K ≤ N` and `n ≤ N` the hypergeometric law has mean `n K / N`. -/
theorem sum_mul_hypergeometricReal {N K n : ℕ} (hN : 0 < N) (hK : K ≤ N) (hn : n ≤ N) :
    ∑ k ∈ range (n + 1), (k : ℝ) * hypergeometricReal N K n k = n * K / N := by
  have hpos : (0 : ℝ) < N.choose n := by exact_mod_cast Nat.choose_pos hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h : (∑ k ∈ range (n + 1), (k * (K.choose k * (N - K).choose (n - k)) : ℝ)) * N =
      n * K * N.choose n := by exact_mod_cast sum_mul_choose_mul_choose hK n
  calc ∑ k ∈ range (n + 1), (k : ℝ) * hypergeometricReal N K n k
      = (∑ k ∈ range (n + 1), (k * (K.choose k * (N - K).choose (n - k)) : ℝ)) /
          N.choose n := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hypergeometricReal, ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hk))]
        ring
    _ = n * K / N := by
        rw [div_eq_div_iff hpos.ne' hNpos.ne', h]

/-- The hypergeometric law on `ℕ` with population size `N`, `K ≤ N` marked items, and
`n ≤ N` draws without replacement. -/
noncomputable def hypergeometric (N K n : ℕ) (hK : K ≤ N) (hn : n ≤ N) : PMF ℕ :=
  PMF.ofFinset (fun k => ENNReal.ofReal (hypergeometricReal N K n k)) (range (n + 1))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hypergeometricReal_nonneg N K n k,
        sum_hypergeometricReal hK hn, ENNReal.ofReal_one])
    (fun k hk => by
      rw [hypergeometricReal_of_lt (by simpa [Nat.lt_succ_iff] using hk), ENNReal.ofReal_zero])

/-- The mass of `k` under `hypergeometric N K n` is `hypergeometricReal N K n k`. -/
theorem hypergeometric_apply {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) (k : ℕ) :
    hypergeometric N K n hK hn k = ENNReal.ofReal (hypergeometricReal N K n k) := rfl

end ProbabilityTheory
