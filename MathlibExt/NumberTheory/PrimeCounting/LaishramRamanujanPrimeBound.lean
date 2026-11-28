/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.RamanujanPrime
import MathlibExt.NumberTheory.PrimeCounting.ExplicitPrimeEstimates
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Laishram's upper bound for Ramanujan primes

The `n`-th Ramanujan prime is strictly below the `3 * n`-th prime. The proof bounds the
number of primes in a dyadic interval using Chebyshev's explicit theta estimates.

For `x ≥ 65536`, partial summation bounds `π(x) log x` from above, while
`θ(2x) - θ(x)` bounds `(π(2x) - π(x)) log(2x)` from below. Together these give
`3 π(x) < 2 π(2x)`. On the finite range we track the minimum of `2 π(2k) - 3 π(k)`
over consecutive blocks.
-/

namespace MetaMathlibExt

namespace laishram_ramanujan_prime_bound

open Real Chebyshev Finset MeasureTheory ExplicitPrimeEstimates

private lemma thetaIntegral_bound {x : ℝ} (hx : 65536 ≤ x) :
    (∫ t in 4096..x, theta t / (t * log t ^ 2)) ≤
      x / (5 * log x) - 4096 / (5 * log 4096) := by
  let f := fun t : ℝ => t / (5 * log t)
  let f' := fun t : ℝ => (log t - 1) / (5 * log t ^ 2)
  have hle : 4096 ≤ x := by linarith
  have hL : 8 < log 4096 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_pow]
    norm_num
    linarith [log_two_gt_d9]
  have hlog {t : ℝ} (ht : 4096 ≤ t) : 8 < log t :=
    hL.trans_le (log_le_log (by norm_num) ht)
  have hint : IntervalIntegrable f' volume 4096 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    have h := hlog ht.1
    dsimp [f']
    fun_prop (disch := first | positivity | linarith [ht.1])
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 4096 x) : HasDerivAt f (f' t) t := by
    rw [Set.uIcc_of_le hle] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hL0 : log t ≠ 0 := by linarith [hlog ht.1]
    convert (hasDerivAt_id t).div ((hasDerivAt_log ht0).const_mul 5) (by positivity : 5 * log t ≠ 0)
      using 1
    · rfl
    · dsimp [f']
      field_simp
  change _ ≤ f x - f 4096
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  apply intervalIntegral.integral_mono_on hle _ hint
  · intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hLt := hlog ht.1
    have hu := theta_le_log4_mul_x ht0.le
    have h4 : log 4 < 1.4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      norm_num
      linarith [log_two_lt_d9]
    dsimp [f']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right
      (hu.trans (mul_le_mul_of_nonneg_right h4.le ht0.le)) (sq_nonneg (log t)),
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hLt.le) ht0.le) (sq_nonneg (log t))]
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (integrableOn_theta_div_id_mul_log_sq x).mono_set
      (Set.Icc_subset_Icc_left (by norm_num))

private lemma primeCounting_upper {x : ℝ} (hx : 65536 ≤ x)
    (hbase : Nat.primeCounting 4096 = 564) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * log x ≤ 1.33 * x := by
  have hx2 : 2 ≤ x := by linarith
  have hL : log 4096 = 12 * log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, log_pow]
    norm_num
  have hLpos : 0 < log x := log_pos (by linarith)
  have hle : 4096 ≤ x := by linarith
  have hint {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t => theta t / (t * log t ^ 2)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc_left ha)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hint (by norm_num : (2 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4096))
    (hint (by norm_num) hle)
  have hbase' := primeCounting_eq_theta_div_log_add_integral (by norm_num : (2 : ℝ) ≤ 4096)
  rw [show ⌊(4096 : ℝ)⌋₊ = 4096 by norm_num, hbase] at hbase'
  have hsmall : (∫ t in (2 : ℝ)..4096, theta t / (t * log t ^ 2)) -
      4096 / (5 * log 4096) ≤ 60 := by
    have hLpos' : 0 < log 4096 := log_pos (by norm_num)
    have : 504 * log 4096 ≤ theta 4096 + 4096 / 5 := by
      linarith [hL, log_two_lt_d9, le_theta_4096]
    apply (mul_le_mul_iff_left₀ hLpos').mp
    field_simp at hbase' ⊢
    linarith
  have he : exp 1 ≤ (65536 : ℝ) := exp_one_lt_three.le.trans (by norm_num)
  have hmono := log_div_self_antitoneOn he (he.trans hx) hx
  change log x / x ≤ log 65536 / 65536 at hmono
  rw [div_le_div_iff₀ (by linarith) (by norm_num),
    show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow] at hmono
  norm_num at hmono
  have herror : 60 * log x ≤ 0.02 * x := by
    nlinarith only [hx, hmono, mul_le_mul_of_nonneg_right log_two_lt_d9.le (show 0 ≤ x by linarith)]
  rw [primeCounting_eq_theta_div_log_add_integral hx2, ← hsum, add_mul,
    div_mul_cancel₀ _ hLpos.ne']
  have hi := thetaIntegral_bound hx
  have : (∫ t in (2 : ℝ)..4096, theta t / (t * log t ^ 2)) +
      (∫ t in 4096..x, theta t / (t * log t ^ 2)) ≤ 60 + x / (5 * log x) := by linarith
  have h := mul_le_mul_of_nonneg_right this hLpos.le
  field_simp at h
  linarith [(theta_bounds_of_65536_le x hx).1]

private lemma theta_difference (a b : ℕ) (hab : a ≤ b) :
    theta b - theta a ≤ (b.primeCounting - a.primeCounting : ℝ) * log b := by
  have hsub := Nat.primesLE_mono hab
  rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log,
    ← Finset.sum_sdiff_eq_sub hsub]
  calc
    _ ≤ ∑ _p ∈ b.primesLE \ a.primesLE, log b := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
      exact log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hp'.1)
    _ = _ := by
      simp [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Nat.monotone_primeCounting hab)]

private lemma large_dyadic {m : ℕ} (hm : 65536 ≤ m) (hbase : Nat.primeCounting 4096 = 564) :
    3 * m.primeCounting < 2 * (2 * m).primeCounting := by
  have hx : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : 16 * log 2 ≤ log m := by
    have h := log_le_log (by norm_num) hx
    rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hθ := (theta_bounds_of_65536_le (m : ℝ) hx).1
  have hθ' := (theta_bounds_of_65536_le (2 * m : ℝ) (by linarith)).2
  have hdiff := theta_difference m (2 * m) (by omega)
  have hπ := primeCounting_upper hx hbase
  rw [Nat.floor_natCast] at hπ
  rw [Nat.cast_mul, Nat.cast_two] at hdiff
  have hlog' : log (2 * m : ℝ) ≤ (17 / 16) * log m := by
    rw [log_mul (by norm_num) (by positivity)]
    linarith
  have hπ' := mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg m.primeCounting)
  by_contra! h
  have h' : 2 * ((2 * m).primeCounting : ℝ) ≤ 3 * (m.primeCounting : ℝ) := by exact_mod_cast h
  have hmul := mul_le_mul_of_nonneg_right h' (log_nonneg (by linarith : (1 : ℝ) ≤ 2 * m))
  linarith

private def surplus (k : ℕ) : ℤ :=
  2 * ((2 * k).primeCounting : ℤ) - 3 * (k.primeCounting : ℤ)

private lemma surplus_step {k : ℕ} (hk : 1 ≤ k) (hb : 2 * (k + 1) < 363 ^ 2) :
    surplus (k + 1) = surplus k + 2 * (primeFlag (2 * k + 1) : ℤ) -
      3 * (primeFlag (k + 1) : ℤ) := by
  have hcount (r : ℕ) : (r + 1).primeCounting = r.primeCounting + if (r + 1).Prime then 1 else 0 :=
    Nat.count_succ _ _
  have heven : ¬ (2 * k + 1 + 1).Prime := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    exact Nat.not_prime_mul (by decide) (by omega)
  simp only [surplus, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, hcount, ite_eq_right heven,
    Nat.add_zero, Nat.cast_add, primeFlag_eq (p := 2 * k + 1) (by omega),
    primeFlag_eq (p := k + 1) (by omega)]
  ring

-- The total change and the least prefix change of the surplus on a block of length 2^d.
private def blockChanges : ℕ → ℕ → ℤ × ℤ
  | 0, k => (2 * (primeFlag (2 * k + 1) : ℤ) - 3 * (primeFlag (k + 1) : ℤ), 0)
  | d + 1, k =>
    let left := blockChanges d k
    let right := blockChanges d (k + 2 ^ d)
    (left.1 + right.1, min left.2 (left.1 + right.2))

private lemma blockChanges_spec (d k : ℕ) (hk : 1 ≤ k) (hb : 2 * (k + 2 ^ d) < 363 ^ 2) :
    (blockChanges d k).1 = surplus (k + 2 ^ d) - surplus k ∧
      ∀ j, k ≤ j → j < k + 2 ^ d → (blockChanges d k).2 ≤ surplus j - surplus k := by
  induction d generalizing k with
  | zero =>
    simp only [pow_zero] at hb ⊢
    constructor
    · dsimp [blockChanges]
      rw [surplus_step hk hb]
      ring
    · intro j hj hj'
      obtain rfl : j = k := by omega
      simp [blockChanges]
  | succ d ih =>
    rw [pow_succ] at hb ⊢
    obtain ⟨hleft, hl⟩ := ih k hk (by omega)
    obtain ⟨hright, hr⟩ := ih (k + 2 ^ d) (by omega) (by omega)
    have hend : k + 2 ^ d + 2 ^ d = k + 2 ^ d * 2 := by omega
    simp only [blockChanges]
    constructor
    · rw [hleft, hright, hend]
      ring
    · intro j hj hj'
      by_cases hm : j < k + 2 ^ d
      · exact (min_le_left ..).trans (hl j hj hm)
      · apply (min_le_right ..).trans
        have := hr j (by omega) (by omega)
        rw [hleft]
        omega

set_option maxHeartbeats 1000000 in
-- Kernel reduction verifies both prime counts throughout the block of length 2^16.
private lemma small_dyadic {m : ℕ} (hm : 21 ≤ m) (hb : m < 65536) :
    3 * m.primeCounting < 2 * (2 * m).primeCounting := by
  have h := (blockChanges_spec 16 21 (by decide) (by decide)).2 m hm (by omega)
  have hstart : surplus 21 = 2 := by decide
  have hmin : 0 < 2 + (blockChanges 16 21).2 := by decide +kernel
  rw [hstart] at h
  unfold surplus at h
  omega

private lemma prime_dyadic {p : ℕ} (hp : p.Prime) :
    3 * (p / 2).primeCounting < 2 * p.primeCounting := by
  by_cases h : p < 42
  · have hsmall : ∀ q < 42, Nat.Prime q →
        3 * (q / 2).primeCounting < 2 * q.primeCounting := by decide
    exact hsmall p h hp
  have hhalf : 3 * (p / 2).primeCounting < 2 * (2 * (p / 2)).primeCounting := by
    rcases lt_or_ge (p / 2) 65536 with hm | hm
    · exact small_dyadic (by omega) hm
    · exact large_dyadic hm primeCounting_4096
  exact hhalf.trans_le (Nat.mul_le_mul_left 2 (Nat.monotone_primeCounting (by omega)))

end laishram_ramanujan_prime_bound

/-- **Laishram's upper bound for Ramanujan primes.** Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$. For all natural numbers $n$ and $R$, if $R$ is the $n$-th Ramanujan prime (which
entails $n \ge 1$), then $R < p_{3n}$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL14/Noe/noe12.tex,
source file SHA-256 b63cf16b83caaaf31e14592b36ef720cdb8c29d7acb1d0c51fad733e550756c6,
THM laishram lines 152-160, exact span SHA-256
4cf034f71bb4dd02bd70f5464b47630035176520d6e76ae976119bc050561a5b,
definition lines 105-117, exact span SHA-256
aa194a945f450eec09898ade174650294052937acdca5139e43f57f9adb760c0,
task jis_grounded_1c4ec8bb1841443d9a65cadf__laishram_ramanujan_prime_bound. -/
public theorem laishram_ramanujan_prime_bound (n R : ℕ)
    (hR : IsNthRamanujanPrime R n) :
    R < Nat.nth Nat.Prime (3 * n - 1) := by
  obtain ⟨hn, ⟨hp, hcount⟩, _⟩ := hR
  have h := laishram_ramanujan_prime_bound.prime_dyadic hp
  apply (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp
  change R.primeCounting ≤ 3 * n - 1
  omega

end MetaMathlibExt
