/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Logarithmic bounds for the maximal gleeful chain length

`MetaMathlibExt.log_maxChainLength_bounds` bounds the logarithm of the largest number of
consecutive prime powers whose sum is at most a given integer.
-/

namespace MetaMathlibExt
namespace log_maxChainLength_bounds

open Real

-- Below 100², every composite number greater than 100 shares a factor with 100!.
private def smallPrime (p : ℕ) : Bool :=
  if p ≤ 100 then decide p.Prime else decide (p ≤ 100 ^ 2 ∧ p.Coprime (Nat.factorial 100))

private lemma smallPrime_sound {p : ℕ} (hp : smallPrime p = true) : p.Prime := by
  unfold smallPrime at hp
  split at hp
  · simpa using hp
  · rename_i hlarge
    obtain ⟨hbound, hcop⟩ := of_decide_eq_true hp
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, fun m hm hroot hdvd ↦ ?_⟩
    have hm' : m ≤ 100 := hroot.trans (by simpa only [Nat.sqrt_eq'] using Nat.sqrt_le_sqrt hbound)
    have := Nat.eq_one_of_dvd_coprimes hcop hdvd (Nat.dvd_factorial (by omega) hm')
    omega

-- Each pair (r, b) certifies that the r-th prime is at most b. The overlaps
-- cover every index from 7 through 1023 using log n ≥ ⌊log₂ n⌋ * log 2.
set_option maxRecDepth 30000 in
private lemma nth_prime_le_small (n : ℕ) (hn : 7 ≤ n) (hn' : n < 1024) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ 2 * n * log n := by
  let blocks : List (ℕ × ℕ) :=
    [(7, 17), (11, 31), (15, 47), (23, 83), (31, 127), (47, 211), (66, 317),
     (99, 523), (139, 797), (213, 1303), (302, 1997), (457, 3229), (653, 4877),
     (991, 7841), (1023, 8147)]
  have counts : ∀ b ∈ blocks, b.1 ≤ Nat.count (fun p ↦ smallPrime p = true) (b.2 + 1) := by
    decide +kernel
  have covers : ∀ i : Fin 1024, 7 ≤ i.val → ∃ b ∈ blocks,
      i.val ≤ b.1 ∧ 3 * b.2 ≤ 4 * i.val * i.val.log2 := by decide +kernel
  obtain ⟨b, hb, hr, hsize⟩ := covers ⟨n, hn'⟩ hn
  have hcount : n ≤ Nat.count Nat.Prime (b.2 + 1) :=
    hr.trans <| (counts b hb).trans <| Nat.count_mono_left fun _ _ ↦ smallPrime_sound
  have hp : Nat.nth Nat.Prime (n - 1) ≤ b.2 :=
    Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (lt_of_lt_of_le (by omega) hcount))
  have hl := Real.log2_le_logb n
  rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))] at hl
  change 3 * b.2 ≤ 4 * n * n.log2 at hsize
  have hsize' : 3 * (b.2 : ℝ) ≤ 4 * n * n.log2 := by exact_mod_cast hsize
  have hlog : 2 / 3 * (n.log2 : ℝ) ≤ log n := by
    refine le_trans ?_ hl
    nlinarith [mul_nonneg (show 0 ≤ log 2 - 2 / 3 by linarith [log_two_gt_d9])
      (Nat.cast_nonneg (α := ℝ) n.log2)]
  calc
    (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ b.2 := by exact_mod_cast hp
    _ ≤ 2 * n * (2 / 3 * (n.log2 : ℝ)) := by linarith
    _ ≤ 2 * n * log n := by gcongr

-- For large n, compare p / log p with t / log t at t = 2n log n
-- using Chebyshev's lower bound on the prime count at p.
private lemma nth_prime_le (n : ℕ) (hn : 7 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ 2 * n * log n := by
  by_cases hsmall : n < 1024
  · exact nth_prime_le_small n hn hsmall
  let p := Nat.nth Nat.Prime (n - 1)
  have hp4 : 4 ≤ p := by
    have := Nat.add_two_le_nth_prime (n - 1)
    dsimp [p]
    omega
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcount : Nat.primeCounting p = n := by
    rw [show Nat.primeCounting p = n - 1 + 1 from
      Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (n - 1)]
    omega
  have hpi := Chebyshev.pi_ge_of_four_le hp4
  rw [hcount, div_le_iff₀ (log_pos (by exact_mod_cast (show 1 < p by omega)))] at hpi
  have hL : 10 * log 2 ≤ log n := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 10)
      (show (2 : ℝ) ^ 10 ≤ n by exact_mod_cast (show 2 ^ 10 ≤ n by omega))
    simpa using h
  have hLpos : 0 < log n := by linarith [log_two_gt_d9]
  let t := 2 * (n : ℝ) * log n
  have ht : 0 < t := by dsimp [t]; positivity
  have htlog : log t < 2 * log 2 * log n := by
    have h16 : log 16 = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
      norm_num
    rw [show t = n * (16 * (log n / 8)) by dsimp [t]; ring,
      log_mul hnR.ne' (by positivity), log_mul (by norm_num) (by positivity), h16]
    nlinarith [log_le_sub_one_of_pos (show 0 < log n / 8 by positivity),
      log_two_gt_d9, log_two_lt_d9,
      mul_nonneg (show 0 ≤ log 2 - 0.693 by linarith [log_two_gt_d9]) hLpos.le]
  change (p : ℝ) ≤ t
  by_contra! hlt
  have he : exp 1 ≤ t := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    dsimp [t]
    nlinarith [exp_one_lt_three, log_two_gt_d9, mul_nonneg (sub_nonneg.mpr hn1) hLpos.le]
  have hmono := log_div_self_antitoneOn he (he.trans hlt.le) hlt.le
  change log p / p ≤ log t / t at hmono
  have ha : log 2 / n ≤ log p / p := (div_le_div_iff₀ hnR hp).mpr (by linarith)
  have hb : log t / t < log 2 / n := by
    rw [div_lt_div_iff₀ ht hnR]
    calc
      log t * n < (2 * log 2 * log n) * n := by gcongr
      _ = log 2 * t := by dsimp [t]; ring
  exact (ha.trans hmono).not_gt hb

private lemma half_pow_lt (k M x : ℕ) (hk : 0 < k) (hM : 6 ≤ M)
    (hx : ∑ i ∈ Finset.range M, Nat.nth Nat.Prime i ^ k ≤ x) :
    ((M : ℝ) / 2) ^ (k + 1) < x := by
  let s := Finset.Ico (M / 2) M
  have hs : s.Nonempty := Finset.nonempty_Ico.mpr (by omega)
  have hcard : (M : ℝ) / 2 ≤ s.card := by
    dsimp [s]
    rw [Nat.card_Ico, div_le_iff₀ (by norm_num)]
    exact_mod_cast (show M ≤ (M - M / 2) * 2 by omega)
  calc
    ((M : ℝ) / 2) ^ (k + 1) = (M / 2 : ℝ) * ((M : ℝ) / 2) ^ k := pow_succ' _ _
    _ ≤ (s.card : ℝ) * ((M : ℝ) / 2) ^ k := by gcongr
    _ = ∑ _i ∈ s, ((M : ℝ) / 2) ^ k := by simp
    _ < ∑ i ∈ s, (Nat.nth Nat.Prime i : ℝ) ^ k := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro i hi
      have hi' := (Finset.mem_Ico.mp hi).1
      apply pow_lt_pow_left₀ _ (by positivity) hk.ne'
      rw [div_lt_iff₀ (by norm_num)]
      exact_mod_cast (show M < Nat.nth Nat.Prime i * 2 by
        have := Nat.add_two_le_nth_prime i
        omega)
    _ ≤ ∑ i ∈ Finset.range M, (Nat.nth Nat.Prime i : ℝ) ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      · intros; positivity
    _ ≤ x := by exact_mod_cast hx

private lemma log_sum_upper (k M x : ℕ) (hM : 6 ≤ M) (hxpos : 0 < (x : ℝ))
    (hx' : x < ∑ i ∈ Finset.range (M + 1), Nat.nth Nat.Prime i ^ k) :
    log x ≤ (k + 1) * log (M + 1 : ℝ) + k * log (2 * log (M + 1 : ℝ)) := by
  have hprime := nth_prime_le (M + 1) (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add_one] at hprime
  have hsum : (x : ℝ) < (M + 1) * (((M + 1) * (2 * log (M + 1 : ℝ))) ^ k) := calc
    (x : ℝ) < ∑ i ∈ Finset.range (M + 1), (Nat.nth Nat.Prime i : ℝ) ^ k := by exact_mod_cast hx'
    _ ≤ ∑ _i ∈ Finset.range (M + 1), ((M + 1) * (2 * log (M + 1 : ℝ))) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (by positivity)
      calc
        (Nat.nth Nat.Prime i : ℝ) ≤ Nat.nth Nat.Prime M := by
          exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ ≤ _ := by linarith
    _ = _ := by simp
  have hlog := (log_lt_log hxpos hsum).le
  have hL : 0 < log (M + 1 : ℝ) := log_pos (by exact_mod_cast (show 1 < M + 1 by omega))
  rw [log_mul (by positivity) (by positivity), log_pow, log_mul (by positivity) (by positivity)]
    at hlog
  linarith

private lemma exp_one_le_two_log {y : ℝ} (hy : 6 ≤ y) : exp 1 ≤ 2 * log (y + 1) := by
  have h := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 2) (show (2 : ℝ) ^ 2 ≤ y + 1 by linarith)
  rw [log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [log_two_gt_d9, exp_one_lt_d9]

-- Multiplying log y by r to reach log m also controls the two logarithms in B.
private lemma scaled_logs {y m r : ℝ} (hy : 6 ≤ y) (hm : y ≤ m)
    (hr : 1 ≤ r) (heq : r * log y = log m) :
    log (m + 1) ≤ r * log (y + 1) ∧ log (2 * log (m + 1)) ≤ r * log (2 * log (y + 1)) := by
  have hypos : 0 < y := by linarith
  have hmpos : 0 < m := hypos.trans_le hm
  have hdiff := log_le_log (by positivity : 0 < (m + 1) / m)
    (show (m + 1) / m ≤ (y + 1) / y from (div_le_div_iff₀ hmpos hypos).mpr (by linarith))
  rw [log_div (by positivity) hmpos.ne', log_div (by positivity) hypos.ne'] at hdiff
  have hsucc : log (m + 1) ≤ r * log (y + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (sub_nonneg.mpr (log_le_log hypos (show y ≤ y + 1 by linarith)))]
  refine ⟨hsucc, ?_⟩
  have hz : 0 < 2 * log (y + 1) := (exp_pos 1).trans_le (exp_one_le_two_log hy)
  have hlogz : 1 ≤ log (2 * log (y + 1)) := (le_log_iff_exp_le hz).mpr (exp_one_le_two_log hy)
  have hrpos : 0 < r := by linarith
  calc
    log (2 * log (m + 1)) ≤ log (r * (2 * log (y + 1))) := by
      apply log_le_log (mul_pos (by norm_num) (log_pos (by linarith)))
      linarith
    _ = log r + log (2 * log (y + 1)) := log_mul hrpos.ne' hz.ne'
    _ ≤ r * log (2 * log (y + 1)) := by
      nlinarith [log_le_sub_one_of_pos hrpos, mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hlogz)]

end log_maxChainLength_bounds

open Real log_maxChainLength_bounds

/-- **Bounds for the logarithm of the maximal gleeful chain length.** Let
$p_1 = 2, p_2 = 3, \dots$ be the primes in increasing order. Let $k > 1$, $M_0 \ge 6$, $M \ge M_0$
and $x$ be natural numbers with $p_1^k + \cdots + p_M^k \le x < p_1^k + \cdots + p_{M+1}^k$.
Put $y = M_0$, let $\log$ be the natural logarithm, and set
$$A = \frac{\log(y/2)}{\log y},$$
$$B = \frac{\log(y+1)}{\log y} + \frac{\log\log((y+1)^2)}{\log y} \cdot \frac{k}{k+1}.$$
Then
$$\frac{\log x}{k+1} \cdot \frac{1}{B} \le \log M < \frac{\log x}{k+1} \cdot \frac{1}{A}.$$

Source: Sara Moore and Jonathan P. Sorenson, *Explicit Bounds and Parallel
Algorithms for Counting Multiply Gleeful Numbers*, INTEGERS 26 (2026), Article A84,
Lemma 3 (`integers-2026-A84-lem-3`), with `A`, `B` from Section 2. -/
public theorem log_maxChainLength_bounds (k M₀ M x : ℕ) (hk : 1 < k) (hM₀ : 6 ≤ M₀)
    (hM : M₀ ≤ M) (hx : ∑ i ∈ Finset.range M, Nat.nth Nat.Prime i ^ k ≤ x)
    (hx' : x < ∑ i ∈ Finset.range (M + 1), Nat.nth Nat.Prime i ^ k) :
    let y : ℝ := M₀
    let A := Real.log (y / 2) / Real.log y
    let B := Real.log (y + 1) / Real.log y +
      Real.log (Real.log ((y + 1) ^ 2)) / Real.log y * ((k : ℝ) / (k + 1))
    Real.log M < Real.log x / (k + 1) * (1 / A) ∧
      Real.log x / (k + 1) * (1 / B) ≤ Real.log M := by
  intro y A B
  have hy : 6 ≤ y := by dsimp [y]; exact_mod_cast hM₀
  have hm : y ≤ (M : ℝ) := by dsimp [y]; exact_mod_cast hM
  have hlogy : 0 < log y := log_pos (by linarith)
  have hlogm := log_le_log (by linarith : 0 < y) hm
  let r := log M / log y
  have hr : 1 ≤ r := (one_le_div hlogy).mpr hlogm
  have heq : r * log y = log M := div_mul_cancel₀ _ hlogy.ne'
  have hA : 0 < A := div_pos (log_pos (by linarith)) hlogy
  have hB : 0 < B := by
    dsimp only [B]
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    have hL := log_pos (show 1 < y + 1 by linarith)
    have hLL := log_pos ((show 1 < exp 1 by linarith [exp_one_gt_two]).trans_le
      (exp_one_le_two_log hy))
    positivity
  have hk' : 0 < (k : ℝ) + 1 := by positivity
  have hhalf := half_pow_lt k M x (by omega) (by omega) hx
  have hbase : 0 < (M : ℝ) / 2 := by linarith
  have hpow : 0 < ((M : ℝ) / 2) ^ (k + 1) := pow_pos hbase _
  constructor
  · rw [mul_one_div, lt_div_iff₀ hA, lt_div_iff₀ hk']
    have hlog := log_lt_log hpow hhalf
    rw [log_pow, Nat.cast_add_one] at hlog
    have hscale : r * log (y / 2) ≤ log ((M : ℝ) / 2) := by
      rw [log_div (by linarith) (by norm_num), log_div (by linarith) (by norm_num)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    calc
      log M * A * (k + 1) = (k + 1) * (r * log (y / 2)) := by dsimp [A, r]; ring
      _ ≤ (k + 1) * log ((M : ℝ) / 2) := by gcongr
      _ < log x := hlog
  · rw [mul_one_div, div_le_iff₀ hB, div_le_iff₀ hk']
    obtain ⟨hs, hls⟩ := scaled_logs hy hm hr heq
    calc
      log x ≤ (k + 1) * log (M + 1 : ℝ) + k * log (2 * log (M + 1 : ℝ)) :=
        log_sum_upper k M x (by omega) (hpow.trans hhalf) hx'
      _ ≤ (k + 1) * (r * log (y + 1)) + k * (r * log (2 * log (y + 1))) := by gcongr
      _ = log M * B * (k + 1) := by
        dsimp only [B, r]
        rw [log_pow]
        push_cast
        field_simp

end MetaMathlibExt
