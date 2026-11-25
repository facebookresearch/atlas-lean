/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Reciprocal totients of primes near the square root

Calzado's reciprocal-totient bound follows from Mertens' estimate for the interval sum of
`Λ(n) / n`. On primes this weight is `log p / p`, and `log p` is comparable to `log x`
throughout the interval.
-/

open Filter Finset Real
open ArithmeticFunction (vonMangoldt vonMangoldt_apply_prime vonMangoldt_nonneg)

namespace MetaMathlibExt

namespace calzado_sum_inv_totient_near_sqrt_isBigO

/-- Subtract the modulus-one Mertens estimate at the two endpoints. -/
private theorem mangoldt_interval_bound :
    ∃ D : ℝ, ∀ y z : ℝ, 1 ≤ y → y ≤ z →
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, vonMangoldt n / n ≤ log z - log y + D := by
  obtain ⟨K, hK⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le (q := 1) 1 isUnit_one
  simp only [Nat.totient_one, Nat.cast_one, div_one, vonMangoldt.residueClass,
    Set.indicator_apply, Set.mem_ofPred_eq, Subsingleton.elim (_ : ZMod 1) 1, ite_true] at hK
  refine ⟨2 * K, fun y z hy hyz ↦ ?_⟩
  have hsplit := sum_Ioc_consecutive (fun n : ℕ ↦ vonMangoldt n / (n : ℝ))
    (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hyz)
  linarith only [hsplit, (abs_le.mp (hK y hy)).1, (abs_le.mp (hK z (hy.trans hyz))).2]

/-- For primes in the interval, the von Mangoldt weight dominates the scaled reciprocal totient. -/
private theorem weighted_totient_sum_le {y z : ℝ} (hy : 1 ≤ y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ z) :
    log y * ∑ p ∈ s, 1 / (Nat.totient p : ℝ) ≤
      2 * ∑ n ∈ Ioc ⌊y⌋₊ ⌊z⌋₊, vonMangoldt n / n := by
  calc
    _ ≤ ∑ p ∈ s, 2 * (vonMangoldt p / p) := by
      rw [mul_sum]
      refine sum_le_sum fun p hp ↦ ?_
      obtain ⟨hprime, hyp, _⟩ := hs p hp
      have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hp₁ : 0 < (p : ℝ) - 1 := by linarith
      have hlog := log_le_log (zero_lt_one.trans_le hy) hyp.le
      rw [vonMangoldt_apply_prime hprime, Nat.totient_prime hprime,
        Nat.cast_sub hprime.one_le, Nat.cast_one, mul_one_div]
      calc
        log y / ((p : ℝ) - 1) ≤ log p / ((p : ℝ) - 1) := by gcongr
        _ ≤ 2 * (log p / p) := by
          have hp₀ : (0 : ℝ) < p := by positivity
          field_simp
          nlinarith [mul_nonneg (log_nonneg (by linarith : (1 : ℝ) ≤ p)) (sub_nonneg.mpr hp₂)]
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨_, hyp, hpz⟩ := hs p hp
        exact mem_Ioc.mpr ⟨(Nat.floor_lt (zero_le_one.trans hy)).mpr hyp, Nat.le_floor hpz⟩
      · exact fun n _ _ ↦ div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

end calzado_sum_inv_totient_near_sqrt_isBigO

open calzado_sum_inv_totient_near_sqrt_isBigO in
/-- **Reciprocal totients of the primes just below $x^{1/2}$.** For every real $B > 0$ there is a
constant $C$ such that for all sufficiently large real $x$, the sum of $1/\varphi(p)$ over the
primes $p$ with $x^{1/2} (\log x)^{-B} < p \le x^{1/2}$ is at most $C \log\log x / \log x$, where
$\varphi$ is Euler's totient function.

Source: Angel Calzado, *A Bombieri-Vinogradov Result to Address the Parity
Problem*, INTEGERS 26 (2026), Article A117, Lemma 1
(`integers-2026-A117-lem-1`). -/
public theorem calzado_sum_inv_totient_near_sqrt_isBigO (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧
          x ^ ((1 : ℝ) / 2) * Real.log x ^ (-B) < (p : ℝ) ∧
            (p : ℝ) ≤ x ^ ((1 : ℝ) / 2)),
        1 / (Nat.totient p : ℝ)
        ≤ C * Real.log (Real.log x) / Real.log x := by
  obtain ⟨D, hD⟩ := mangoldt_interval_bound
  refine ⟨8 * (B + 1), ?_⟩
  have hsmall := (isLittleO_log_id_atTop.bound (by positivity : 0 < (1 / 4 : ℝ) / B))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (max 1 D),
    tendsto_log_atTop.eventually hsmall] with x hx hlarge hsmall
  have hx₀ := zero_lt_one.trans hx
  have hL := log_pos hx
  have hLL : 1 ≤ log (log x) := (le_max_left 1 D).trans hlarge
  have hD' : D ≤ log (log x) := (le_max_right 1 D).trans hlarge
  simp only [Real.norm_eq_abs, id_eq, abs_of_pos hL, abs_of_nonneg (zero_le_one.trans hLL)]
    at hsmall
  have hscale : B * log (log x) ≤ log x / 4 := by
    have := mul_le_mul_of_nonneg_right hsmall hB.le
    field_simp [hB.ne'] at this
    linarith
  let z := x ^ ((1 : ℝ) / 2)
  let y := z * log x ^ (-B)
  have hz₀ : 0 < z := rpow_pos_of_pos hx₀ _
  have hy₀ : 0 < y := mul_pos hz₀ (rpow_pos_of_pos hL _)
  have hzlog : log z = (1 / 2 : ℝ) * log x := log_rpow hx₀ _
  have hylog : log y = log z - B * log (log x) := by
    rw [show y = z * log x ^ (-B) from rfl, log_mul hz₀.ne' (rpow_pos_of_pos hL _).ne',
      log_rpow hL]
    ring
  have hylog' : log x ≤ 4 * log y := by linarith
  have hy : 1 ≤ y := (log_nonneg_iff hy₀).mp (by linarith)
  have hyz : y ≤ z := (log_le_log_iff hy₀ hz₀).mp (by nlinarith)
  let s := (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ ↦ p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ z)
  have hs := weighted_totient_sum_le hy s (fun p hp ↦ (mem_filter.mp hp).2)
  have hsum : 0 ≤ ∑ p ∈ s, 1 / (Nat.totient p : ℝ) := sum_nonneg fun _ _ ↦ by positivity
  change (∑ p ∈ s, 1 / (Nat.totient p : ℝ)) ≤ _
  rw [le_div_iff₀ hL]
  linarith only [mul_le_mul_of_nonneg_right hylog' hsum, hs, hD y z hy hyz, hylog, hD']

end MetaMathlibExt
