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
* `sum_mul_sub_one_mul_hypergeometricReal`: the second factorial moment is
  `n (n - 1) K (K - 1) / (N (N - 1))` (for `N > 1`).
* `sum_sq_sub_mean_mul_hypergeometricReal`: the variance is `n K (N - K) (N - n) / (N² (N - 1))`
  (for `N > 1`).

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

/-- The second-factorial-moment identity
`(∑ₖ k (k - 1) C(K, k) C(N - K, n - k)) N (N - 1) = n (n - 1) K (K - 1) C(N, n)`. -/
private lemma sum_descFactorial_mul_choose_mul_choose {N K : ℕ} (hK : K ≤ N) (n : ℕ) :
    (∑ k ∈ range (n + 1), k * (k - 1) * (K.choose k * (N - K).choose (n - k))) * (N * (N - 1)) =
      n * (n - 1) * (K * (K - 1)) * N.choose n := by
  rcases n with _ | _ | n
  · simp
  · simp [Finset.sum_range_succ]
  rcases K with _ | _ | K
  · rw [Finset.sum_eq_zero fun k _ => by rcases k with _ | k <;> simp]
    simp
  · rw [Finset.sum_eq_zero fun k _ => by
      rcases k with _ | _ | k
      · simp
      · simp
      · simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k + 1 + 1)]]
    simp
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 2 := ⟨N - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hterm : ∀ k ∈ range (n + 1), (k + 1 + 1) * (k + 1 + 1 - 1) *
      ((K + 1 + 1).choose (k + 1 + 1) * (N + 2 - (K + 1 + 1)).choose (n + 1 + 1 - (k + 1 + 1))) =
      (K + 1 + 1) * (K + 1) * (K.choose k * (N - K).choose (n - k)) := by
    intro k _
    have h1 := Nat.add_one_mul_choose_eq K k
    have h2 := Nat.add_one_mul_choose_eq (K + 1) (k + 1)
    rw [Nat.add_sub_cancel, show N + 2 - (K + 1 + 1) = N - K by omega, Nat.add_sub_add_right,
      Nat.add_sub_add_right]
    calc (k + 1 + 1) * (k + 1) * ((K + 1 + 1).choose (k + 1 + 1) * (N - K).choose (n - k))
        = ((K + 1 + 1).choose (k + 1 + 1) * (k + 1 + 1)) * (k + 1) *
            (N - K).choose (n - k) := by ring
      _ = (K + 1 + 1) * ((K + 1).choose (k + 1) * (k + 1)) * (N - K).choose (n - k) := by
          rw [← h2]; ring
      _ = _ := by rw [← h1]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_choose_mul_choose (by omega : K ≤ N) n]
  have h3 := Nat.add_one_mul_choose_eq N n
  have h4 := Nat.add_one_mul_choose_eq (N + 1) (n + 1)
  have key : (N + 1 + 1) * (N + 1) * N.choose n =
      (N + 1 + 1).choose (n + 1 + 1) * (n + 1 + 1) * (n + 1) := by
    rw [mul_assoc, h3, ← mul_assoc, h4]
  simp only [mul_zero, zero_mul, add_zero, Nat.add_sub_cancel]
  calc (K + 1 + 1) * (K + 1) * N.choose n * ((N + 2) * (N + 1))
      = (K + 1 + 1) * (K + 1) * ((N + 1 + 1) * (N + 1) * N.choose n) := by ring
    _ = _ := by rw [key]; ring

/-- **Second factorial moment.** For `1 < N`, `K ≤ N` and `n ≤ N` the hypergeometric law has
`E[X (X - 1)] = n (n - 1) K (K - 1) / (N (N - 1))`. -/
theorem sum_mul_sub_one_mul_hypergeometricReal {N K n : ℕ} (hN : 1 < N) (hK : K ≤ N)
    (hn : n ≤ N) :
    ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * hypergeometricReal N K n k =
      n * (n - 1) * (K * (K - 1)) / (N * (N - 1)) := by
  have hpos : (0 : ℝ) < N.choose n := by exact_mod_cast Nat.choose_pos hn
  have hNpos : (0 : ℝ) < N * (N - 1) := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    nlinarith
  have hcast : ∀ m : ℕ, (m : ℝ) * ((m - 1 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := fun m => by
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel]; push_cast; ring
  have h := sum_descFactorial_mul_choose_mul_choose hK n
  have h' : (∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) *
      (K.choose k * (N - K).choose (n - k) : ℝ)) * (N * (N - 1)) =
      n * (n - 1) * (K * (K - 1)) * N.choose n := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_sum, hcast] using this
  calc ∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) * hypergeometricReal N K n k
      = (∑ k ∈ range (n + 1), (k : ℝ) * ((k : ℝ) - 1) *
          (K.choose k * (N - K).choose (n - k) : ℝ)) / N.choose n := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hypergeometricReal, ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hk))]
        ring
    _ = n * (n - 1) * (K * (K - 1)) / (N * (N - 1)) := by
        rw [div_eq_div_iff hpos.ne' hNpos.ne', h']

/-- **Variance.** For `1 < N`, `K ≤ N` and `n ≤ N` the hypergeometric law has variance
`n K (N - K) (N - n) / (N² (N - 1))`. -/
theorem sum_sq_sub_mean_mul_hypergeometricReal {N K n : ℕ} (hN : 1 < N) (hK : K ≤ N)
    (hn : n ≤ N) :
    ∑ k ∈ range (n + 1), ((k : ℝ) - n * K / N) ^ 2 * hypergeometricReal N K n k =
      n * K * ((N : ℝ) - K) * ((N : ℝ) - n) / ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by
  have h0 := sum_hypergeometricReal hK hn
  have h1 := sum_mul_hypergeometricReal (by omega) hK hn
  have h2 := sum_mul_sub_one_mul_hypergeometricReal hN hK hn
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by omega : N ≠ 1))
  have hexp : ∀ k ∈ range (n + 1), ((k : ℝ) - n * K / N) ^ 2 * hypergeometricReal N K n k =
      (k : ℝ) * ((k : ℝ) - 1) * hypergeometricReal N K n k +
        (1 - 2 * (n * K / N)) * ((k : ℝ) * hypergeometricReal N K n k) +
          (n * K / N) ^ 2 * hypergeometricReal N K n k := fun k _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, h0, h1, h2]
  field_simp
  ring

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
