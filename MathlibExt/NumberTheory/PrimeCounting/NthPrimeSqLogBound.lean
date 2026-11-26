/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.NumberTheory.PrimeCounting.ChebyshevThetaBounds

/-!
# An explicit inequality between an index and the corresponding prime

`MetaMathlibExt.nthPrime_sq_log_bound` proves Zhang and Xiong's polynomial inequality by bounding
the normalized prime count with Chebyshev's explicit estimate and Abel summation.
-/

namespace MetaMathlibExt
namespace nthPrime_sq_log_bound

open Real MeasureTheory

private lemma log_sixtyFour : log 64 = 6 * log 2 := by
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num, log_pow]
  norm_num

-- A lower Taylor polynomial for the exponential absorbs the logarithmic errors for L ≥ 7.
private lemma log_error {L : ℝ} (hL : 7 ≤ L) :
    L ^ 3 + 5 / 2 * L ^ 2 + 2 * L ≤ 2 * exp L := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hL
  have hs := sum_le_exp_of_nonneg (by positivity : 0 ≤ 7 + d) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  apply le_trans _ (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2))
  rw [← sub_nonneg]
  ring_nf
  positivity

private lemma theta_bound {x : ℝ} (hx : 1 < x) :
    Chebyshev.theta x ≤ 1.11 * x + 2 * x / log x := by
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hL := log_pos hx
  rcases le_or_gt (log x) 7 with h | h
  · refine (Chebyshev.theta_le_log4_mul_x hx₀.le).trans ?_
    rw [log_four_eq]
    have hc : 2 * log 2 ≤ 1.39 := by linarith only [log_two_lt_d9]
    have he : 0.28 ≤ 2 / log x := (le_div_iff₀ hL).2 (by linarith)
    linarith only [mul_le_mul_of_nonneg_right hc hx₀.le,
      mul_le_mul_of_nonneg_right he hx₀.le, show 2 / log x * x = 2 * x / log x by ring]
  let A := log (((2 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) * (5 : ℝ) ^ (1 / 5 : ℝ)) /
    (30 : ℝ) ^ (1 / 30 : ℝ))
  have hA : A = 7 / 15 * log 2 + 3 / 10 * log 3 + 1 / 6 * log 5 := by
    dsimp only [A]
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity)]
    simp only [log_rpow (by norm_num : (0 : ℝ) < 2), log_rpow (by norm_num : (0 : ℝ) < 3),
      log_rpow (by norm_num : (0 : ℝ) < 5), log_rpow (by norm_num : (0 : ℝ) < 30)]
    rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, log_mul (by norm_num) (by norm_num),
      log_mul (by norm_num) (by norm_num)]
    ring
  have hA₀ : 0 ≤ A := by rw [hA]; positivity
  have hA₁ : 6 / 5 * A ≤ 1.11 := by
    linarith only [hA, log_two_lt_d9, log_three_lt_d9, log_five_lt_d9]
  have h₆ : 5 / (4 * log 6) ≤ 1 := by
    have hl := log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 6)
    rw [log_four_eq] at hl
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hl, log_two_gt_d9]
  have he := log_error h.le
  rw [exp_log hx₀] at he
  have herr : (log x) ^ 2 + 5 / 2 * log x + 2 ≤ 2 * x / log x := by
    apply (le_div_iff₀ hL).2
    linarith only [he]
  linarith only [(chebyshev_theta_explicit_bounds x hx).1, mul_nonneg hA₀ (sqrt_nonneg x),
    mul_le_mul_of_nonneg_right hA₁ hx₀.le, mul_le_mul_of_nonneg_right h₆ (sq_nonneg (log x)),
    herr]

-- At 64 the explicit count and primorial give the starting value for Abel summation.
private lemma integral_base :
    (∫ t : ℝ in 2..64, Chebyshev.theta t / (t * log t ^ 2)) ≤ 3 * 64 / log 64 ^ 2 := by
  have hp : (64 : ℕ) ^ 8 ≤ primorial 64 := by decide
  have hθ : 8 * log 64 ≤ Chebyshev.theta 64 := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_ofNat]
    have hp' : (64 : ℝ) ^ 8 ≤ (primorial 64 : ℝ) := by exact_mod_cast hp
    have h := log_le_log (by positivity) hp'
    simpa only [log_pow, Nat.cast_ofNat] using h
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral (by norm_num : (2 : ℝ) ≤ 64)
  rw [Nat.floor_ofNat, show Nat.primeCounting 64 = 18 by decide] at hπ
  have h₁ : (8 : ℝ) ≤ Chebyshev.theta 64 / log 64 :=
    (le_div_iff₀ (by positivity)).2 hθ
  have h₂ : log 64 ≤ 4.2 := by rw [log_sixtyFour]; linarith only [log_two_lt_d9]
  apply le_trans (b := 10) (by linarith only [hπ, h₁])
  apply (le_div_iff₀ (by positivity)).2
  nlinarith only [sq_le_sq' (by linarith [log_pos (by norm_num : (1 : ℝ) < 64)]) h₂]

-- Above 64, the derivative of 3x / (log x)² dominates the Abel summation integrand.
private lemma integral_bound {x : ℝ} (hx : 64 ≤ x) :
    (∫ t in 2..x, Chebyshev.theta t / (t * log t ^ 2)) ≤ 3 * x / log x ^ 2 := by
  let D (t : ℝ) := (3 * log t - 6) / log t ^ 3
  have hlog {t : ℝ} (ht : 64 ≤ t) : 4 ≤ log t := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 64) ht
    rw [log_sixtyFour] at h
    linarith only [h, log_two_gt_d9]
  have hint {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun t ↦ Chebyshev.theta t / (t * log t ^ 2)) volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [Set.uIoc_of_le hab, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc_left ha)
  have hD : IntervalIntegrable D volume 64 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' := ((Set.uIcc_of_le hx ▸ ht).1 : 64 ≤ t)
    have ht₀ : 0 < t := by linarith
    have hL : 0 < log t := by linarith only [hlog ht']
    dsimp [D]
    fun_prop (disch := positivity)
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc 64 x) :
      HasDerivAt (fun y : ℝ ↦ 3 * y / log y ^ 2) (D t) t := by
    have ht' := ((Set.uIcc_of_le hx ▸ ht).1 : 64 ≤ t)
    have ht₀ : 0 < t := by linarith
    have hL : 0 < log t := by linarith only [hlog ht']
    convert (((hasDerivAt_id t).const_mul 3).div
      ((hasDerivAt_log ht₀.ne').pow 2) (pow_ne_zero _ hL.ne')) using 1
    · rfl
    · dsimp [D]
      field_simp
      ring
  have htail := intervalIntegral.integral_mono_on hx (hint (by norm_num) hx) hD
    (fun t ht ↦ show Chebyshev.theta t / (t * log t ^ 2) ≤ D t by
      have ht₀ : 0 < t := by linarith [ht.1]
      have hL₄ := hlog ht.1
      have hL : 0 < log t := by linarith
      have hθ := Chebyshev.theta_le_log4_mul_x ht₀.le
      rw [log_four_eq] at hθ
      have hθ' : Chebyshev.theta t ≤ 1.5 * t :=
        hθ.trans (mul_le_mul_of_nonneg_right (by linarith only [log_two_lt_d9]) ht₀.le)
      calc
        _ ≤ 1.5 * t / (t * log t ^ 2) := by gcongr
        _ ≤ D t := by
          dsimp [D]
          field_simp
          linarith only [hL₄])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hD] at htail
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint le_rfl (by norm_num : (2 : ℝ) ≤ 64))
    (hint (by norm_num) hx)]
  linarith only [integral_base, htail]

private lemma primeCounting_bound {x : ℝ} (hx : 64 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ * log x / x ≤ 1.11 + 5 / log x := by
  have hx₁ : 1 < x := by linarith
  have hx₀ := zero_lt_one.trans hx₁
  have hL := log_pos hx₁
  have hπ := Chebyshev.primeCounting_eq_theta_div_log_add_integral (by linarith : 2 ≤ x)
  rw [hπ]
  calc
    _ ≤ ((1.11 * x + 2 * x / log x) / log x + 3 * x / log x ^ 2) * log x / x := by
      gcongr
      · exact theta_bound hx₁
      · exact integral_bound hx
    _ = _ := by field_simp; ring

private lemma small_primeCounting_bound {p : ℕ} (hp : 2 ≤ p) (hp' : p < 64) :
    Nat.primeCounting p * log p / p ≤ 2.1 := by
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hL : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  apply (div_le_iff₀ hp₀).2
  by_cases h : p < 8
  · have hcount : ∀ k : Fin 8, Nat.primeCounting k ≤ k.val := by decide
    have hπ : (Nat.primeCounting p : ℝ) ≤ p := by exact_mod_cast hcount ⟨p, h⟩
    have hlog := log_le_log hp₀ (by exact_mod_cast h.le : (p : ℝ) ≤ 8)
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow, Nat.cast_ofNat] at hlog
    have hL' : log (p : ℝ) ≤ 2.1 := by linarith only [hlog, log_two_lt_d9]
    simpa only [mul_comm (2.1 : ℝ)] using mul_le_mul hπ hL' hL hp₀.le
  · have hcount : ∀ k : Fin 64, 8 ≤ k.val → 2 * Nat.primeCounting k ≤ k.val := by decide
    have hπ : 2 * (Nat.primeCounting p : ℝ) ≤ p := by
      exact_mod_cast hcount ⟨p, hp'⟩ (Nat.le_of_not_gt h)
    have hlog := log_le_log hp₀ (by exact_mod_cast hp'.le : (p : ℝ) ≤ 64)
    rw [log_sixtyFour] at hlog
    have hL' : log (p : ℝ) ≤ 4.2 := by linarith only [hlog, log_two_lt_d9]
    linarith only [mul_le_mul_of_nonneg_right hπ hL, mul_le_mul_of_nonneg_right hL' hp₀.le]

-- Compare the quadratic in the normalized count t with its value at 1.11.
private lemma polynomial_bound {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (h : (t ≤ 2.1 ∧ L ≤ 4.2) ∨ (4 ≤ L ∧ t ≤ 1.11 + 5 / L)) :
    (118.676119576 * t ^ 2 + 709.7856 * t) * L < 937.5 * L + 5674.5 := by
  let F (u : ℝ) := 118.676119576 * u ^ 2 + 709.7856 * u
  change F t * L < _
  rcases h with ⟨ht', hL'⟩ | ⟨hL', ht'⟩
  · have hf : F t ≤ F 2.1 := by dsimp [F]; gcongr
    have h := mul_le_mul_of_nonneg_right hf hL.le
    dsimp [F] at h ⊢
    linarith only [h, hL']
  · have he : (t - 1.11) * L ≤ 5 := (le_div_iff₀ hL).mp (by linarith only [ht'])
    have ht₁ : t ≤ 2.36 := by
      have : 5 / L ≤ 1.25 := (div_le_iff₀ hL).2 (by linarith)
      linarith
    have hs : 0 ≤ 118.676119576 * (t + 1.11) + 709.7856 := by positivity
    have hf : (F t - F 1.11) * L ≤ 5 * (118.676119576 * (t + 1.11) + 709.7856) := by
      dsimp [F]
      linarith only [mul_le_mul_of_nonneg_right he hs]
    dsimp [F] at hf ⊢
    linarith only [hf, ht₁, hL']

end nthPrime_sq_log_bound

open nthPrime_sq_log_bound in
/-- **An explicit inequality between $n$ and the $n$th prime.** For every integer $n \ge 1$, the
$n$th prime $p_n$ (counting from $p_1 = 2$) satisfies
$$118.676119576 \, n^2 (\log p_n)^3 + 709.7856 \, n \, p_n (\log p_n)^2
< 937.5 \, p_n^2 \log p_n + 5674.5 \, p_n^2.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 1 (`integers-2025-A58-prop-1`). -/
public theorem nthPrime_sq_log_bound (n : ℕ) (hn : 1 ≤ n) :
    118.676119576 * (n : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 3 +
        709.7856 * n * (Nat.nth Nat.Prime (n - 1) : ℝ) *
          Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 <
      937.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) +
        5674.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 := by
  let p := Nat.nth Nat.Prime (n - 1)
  have hp : 2 ≤ p := (Nat.prime_nth_prime _).two_le
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hπ : Nat.primeCounting p = n := by
    exact (Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime (n - 1)).trans (by omega)
  let L := Real.log (p : ℝ)
  let t := n * L / p
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < p))
  have ht : 0 ≤ t := by positivity
  have h := polynomial_bound hL ht (by
    by_cases hs : p < 64
    · left
      refine ⟨by simpa only [hπ] using small_primeCounting_bound hp hs, ?_⟩
      have hlog := Real.log_le_log hp₀ (by exact_mod_cast hs.le : (p : ℝ) ≤ 64)
      rw [log_sixtyFour] at hlog
      linarith only [hlog, Real.log_two_lt_d9]
    · right
      have h₆₄ : (64 : ℝ) ≤ p := by exact_mod_cast (by omega : 64 ≤ p)
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 64) h₆₄
      rw [log_sixtyFour] at hlog
      exact ⟨by linarith only [hlog, Real.log_two_gt_d9],
        by simpa only [Nat.floor_natCast, hπ] using primeCounting_bound h₆₄⟩)
  change 118.676119576 * (n : ℝ) ^ 2 * L ^ 3 + 709.7856 * n * p * L ^ 2 <
    937.5 * (p : ℝ) ^ 2 * L + 5674.5 * (p : ℝ) ^ 2
  dsimp only [t] at h
  field_simp at h
  linarith only [h]

end MetaMathlibExt
