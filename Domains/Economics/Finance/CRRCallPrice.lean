/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.BinomialReplication
public import Domains.Economics.Finance.OptionPayoffs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cox–Ross–Rubinstein call price

Backward induction gives a discounted binomial sum. On the in-the-money tail, the stock part of
the payoff tilts the risk-neutral weights, while the strike part keeps the original weights.
-/

namespace MathlibExt.Probability.Finance.BinomialReplication

open Finset OptionPayoffs
open scoped BigOperators

private theorem sum_choose_succ (q r : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range (n + 2), ((n + 1).choose j : ℝ) * q ^ j * r ^ (n + 1 - j) * f j =
      q * (∑ j ∈ range (n + 1), (n.choose j : ℝ) * q ^ j * r ^ (n - j) * f (j + 1)) +
        r * (∑ j ∈ range (n + 1), (n.choose j : ℝ) * q ^ j * r ^ (n - j) * f j) := by
  have hdown :
      ∑ j ∈ range (n + 2), (n.choose j : ℝ) * q ^ j * r ^ (n + 1 - j) * f j =
        r * (∑ j ∈ range (n + 1), (n.choose j : ℝ) * q ^ j * r ^ (n - j) * f j) := by
    rw [sum_range_succ, mul_sum]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := mem_range.mp hj
    rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
    ring
  rw [← hdown, mul_sum,
    sum_range_succ' (fun j => ((n + 1).choose j : ℝ) * q ^ j * r ^ (n + 1 - j) * f j),
    sum_range_succ' (fun j => (n.choose j : ℝ) * q ^ j * r ^ (n + 1 - j) * f j)]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, one_mul]
  rw [← add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right, pow_succ q j]
  ring

private theorem claimValue_price_eq_sum (S₀ u d R : ℝ) (V : ℝ → ℝ) (n : ℕ)
    (s : List Bool) :
    let p := rnProb u d R
    claimValue u d R (fun t => V (price S₀ u d t)) n s =
      (∑ j ∈ range (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) *
        V (price S₀ u d s * u ^ j * d ^ (n - j))) / R ^ n := by
  dsimp only
  induction n generalizing s with
  | zero => simp [claimValue]
  | succ n ih =>
    rw [claimValue, ih (true :: s), ih (false :: s), pow_succ, sum_choose_succ]
    simp only [price, ← mul_div_assoc, ← add_div, div_div]
    congr 1
    congr 1
    · congr 1
      refine sum_congr rfl fun j _ => ?_
      congr 1
      congr 1
      rw [Nat.add_sub_add_right, pow_succ u j]
      ring
    · congr 1
      refine sum_congr rfl fun j hj => ?_
      have hj' : j < n + 1 := mem_range.mp hj
      congr 1
      congr 1
      rw [show n + 1 - j = n - j + 1 by omega, pow_succ]
      ring

private theorem exists_call_cutoff {S₀ u d K : ℝ} (hS₀ : 0 < S₀) (hd : 0 < d)
    (hdu : d < u) (n : ℕ) :
    ∃ a : ℕ, a ≤ n + 1 ∧ ∀ j ≤ n, a ≤ j ↔ K < S₀ * u ^ j * d ^ (n - j) := by
  classical
  let T (j : ℕ) := S₀ * u ^ j * d ^ (n - j)
  have hu := hd.trans hdu
  have step (j : ℕ) (hj : j < n) : T j < T (j + 1) := by
    have hT : 0 < T j := by
      dsimp [T]
      positivity
    have hstep : T j * u = T (j + 1) * d := by
      dsimp [T]
      rw [show n - j = n - (j + 1) + 1 by omega, pow_succ, pow_succ u j]
      ring
    exact lt_of_mul_lt_mul_right ((mul_lt_mul_of_pos_left hdu hT).trans_eq hstep) hd.le
  have mono (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : T i ≤ T j := by
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih =>
      have hj' : j < n := by omega
      exact (ih hj'.le).trans (step j hj').le
  by_cases hex : ∃ j ≤ n, K < T j
  · have ha := Nat.find_spec hex
    refine ⟨Nat.find hex, ha.1.trans (Nat.le_succ n), fun j hj => ⟨?_, ?_⟩⟩
    · intro haj
      exact ha.2.trans_le (mono _ _ haj hj)
    · intro hKj
      exact Nat.find_min' hex ⟨hj, hKj⟩
  · refine ⟨n + 1, le_rfl, fun j hj => ⟨?_, ?_⟩⟩
    · omega
    · intro hKj
      exact (hex ⟨j, hj, hKj⟩).elim

/-- **Cox–Ross–Rubinstein call price** (Cox, Ross and Rubinstein 1979): for positive initial price
and strike and `0 < d < R < u`, let `p = (R - d) / (u - d)` and `p' = p * u / R`. On the finite
range `0 ≤ j ≤ n`, the terminal price with `j` up moves is strictly above the strike exactly when
`a ≤ j`. This determines `a` as the first such index, or `n + 1` if none qualifies. The
backward-induction value of the European call is the initial price times the upper binomial tail
at `p'`, minus the discounted strike times the same tail at `p`. Both tails are empty, and the
value is zero, when `a = n + 1`. -/
public theorem claimValue_call_eq_binomialTails {S₀ u d R K : ℝ} (hS₀ : 0 < S₀)
    (hd : 0 < d) (hdR : d < R) (hRu : R < u) (_hK : 0 < K) (n : ℕ) :
    let p := rnProb u d R
    let p' := p * u / R
    let tail (a : ℕ) (q : ℝ) :=
      ∑ j ∈ Ico a (n + 1), (n.choose j : ℝ) * q ^ j * (1 - q) ^ (n - j)
    let value := claimValue u d R (fun s => europeanCallPayoff (price S₀ u d s) K) n []
    ∃ a : ℕ, a ≤ n + 1 ∧ (∀ j ≤ n, a ≤ j ↔ K < S₀ * u ^ j * d ^ (n - j)) ∧
      value = S₀ * tail a p' - K / R ^ n * tail a p ∧ (a = n + 1 → value = 0) := by
  classical
  dsimp only
  let p := rnProb u d R
  let p' := p * u / R
  have hR := hd.trans hdR
  have hdu := hdR.trans hRu
  have hdown : 1 - p' = (1 - p) * d / R := by
    dsimp [p', p, rnProb]
    field_simp [hR.ne', (sub_pos.mpr hdu).ne']
    ring
  obtain ⟨a, ha, hcut⟩ := exists_call_cutoff (K := K) hS₀ hd hdu n
  refine ⟨a, ha, hcut, ?_⟩
  suffices hvalue :
      claimValue u d R (fun s => europeanCallPayoff (price S₀ u d s) K) n [] =
        S₀ * (∑ j ∈ Ico a (n + 1), (n.choose j : ℝ) * p' ^ j * (1 - p') ^ (n - j)) -
          K / R ^ n * (∑ j ∈ Ico a (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)) by
    refine ⟨hvalue, fun ha' => ?_⟩
    simp [hvalue, ha']
  rw [claimValue_price_eq_sum S₀ u d R (fun x => europeanCallPayoff x K)]
  simp only [price]
  have hfilter : (range (n + 1)).filter (a ≤ ·) = Ico a (n + 1) := by
    ext j
    simp [and_comm]
  have hpay :
      (∑ j ∈ range (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) *
        europeanCallPayoff (S₀ * u ^ j * d ^ (n - j)) K) =
      ∑ j ∈ Ico a (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j) *
        (S₀ * u ^ j * d ^ (n - j) - K) := by
    rw [← hfilter, sum_filter]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    by_cases haj : a ≤ j
    · rw [ite_eq_left haj, europeanCallPayoff, max_eq_left]
      exact (sub_pos.mpr ((hcut j hj').mp haj)).le
    · rw [ite_eq_right haj, europeanCallPayoff, max_eq_right, mul_zero]
      exact sub_nonpos.mpr (le_of_not_gt fun h => haj ((hcut j hj').mpr h))
  change _ / R ^ n = S₀ * (∑ j ∈ Ico a (n + 1),
    (n.choose j : ℝ) * p' ^ j * (1 - p') ^ (n - j)) -
    K / R ^ n * (∑ j ∈ Ico a (n + 1), (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j))
  rw [hpay, div_eq_mul_inv, sum_mul, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_Ico.mp hj).2
  have hpow : R ^ j * R ^ (n - j) = R ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hj']
  rw [hdown]
  dsimp only [p']
  rw [div_pow, div_pow, mul_pow, mul_pow]
  rw [div_eq_mul_inv K, ← hpow]
  field_simp [hR.ne']

end MathlibExt.Probability.Finance.BinomialReplication
