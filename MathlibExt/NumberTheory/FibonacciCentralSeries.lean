/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Fib.Basic
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Fibonacci numbers and `π²`

The two factorial series with even and odd Fibonacci indices evaluate to multiples of `π²`.

Statements from Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024),
no. 1 (paper `tonien10292023`), read from the extracted text layer (the primary PDF is not
reachable for agents). The second identity is the continuation line `= …` of the aligned display
that starts with `π² =`; the text layer drops the repeated left side.
-/

open Real
open scoped goldenRatio

namespace MetaMathlibExt
namespace pi_sq_eq_fibonacci_central_series

private noncomputable def coeff (k : ℕ) : ℝ :=
  (k.factorial : ℝ) ^ 2 / (2 * k + 2).factorial

/-- Integrate Lehmer's series after dividing by its argument. -/
private lemma hasSum_arcsin_sq {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    HasSum (fun k : ℕ ↦ coeff k * (2 * x) ^ (2 * k + 2)) (2 * arcsin x ^ 2) := by
  let c (k : ℕ) : ℝ := 2 ^ (2 * k + 2) /
    ((k + 1 : ℝ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℝ))
  let f (k : ℕ) (t : ℝ) := c k * t ^ (2 * k + 1)
  let g (t : ℝ) := 2 * arcsin t / √(1 - t ^ 2)
  have hsum {t : ℝ} (ht : 0 < t) (ht' : t < 1) : HasSum (fun k ↦ f k t) (g t) := by
    have h := (arcsin_central_binomial_reciprocal_series t
      (by rwa [abs_of_pos ht])).div_const t
    convert h using 1
    · funext k
      dsimp [f, c]
      rw [mul_pow, show 2 * (k + 1) = 2 * k + 2 by omega]
      push_cast
      rw [pow_succ t (2 * k + 1)]
      field_simp
    · dsimp [g]
      field_simp
  have hle {t : ℝ} (ht : t ∈ Set.uIcc 0 x) : 0 ≤ t ∧ t ≤ x := by
    rwa [Set.uIcc_of_le hx.le] at ht
  have hgt {t : ℝ} (ht : t ∈ Set.uIoc 0 x) : 0 < t ∧ t ≤ x := by
    rwa [Set.uIoc_of_le hx.le] at ht
  have hsq {t : ℝ} (ht : t ∈ Set.uIcc 0 x) : 0 < 1 - t ^ 2 := by
    obtain ⟨ht₀, htx⟩ := hle ht
    nlinarith [mul_pos (sub_pos.mpr (htx.trans_lt hx')) (show 0 < 1 + t by linarith)]
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := x) (μ := MeasureTheory.volume) (F := f) (f := g)
    (fun k _ ↦ f k x)
    (fun k ↦ (show Continuous (f k) by dsimp [f]; fun_prop).aestronglyMeasurable)
    (fun k ↦ MeasureTheory.ae_of_all _ fun t ht ↦ by
      obtain ⟨ht₀, htx⟩ := hgt ht
      have hc : 0 ≤ c k := by dsimp [c]; positivity
      dsimp [f]
      rw [abs_of_nonneg (by positivity)]
      gcongr)
    (MeasureTheory.ae_of_all _ fun _ _ ↦ (hsum hx hx').summable)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun _ ht ↦ hsum (hgt ht).1 ((hgt ht).2.trans_lt hx'))
  have hg : ∫ t in 0..x, g t = arcsin x ^ 2 := by
    have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 x) :
        HasDerivAt (fun y ↦ arcsin y ^ 2) (g t) t := by
      have ha := Real.hasDerivAt_arcsin (x := t) (by linarith [(hle ht).1])
        (ne_of_lt ((hle ht).2.trans_lt hx'))
      convert ha.pow 2 using 1
      dsimp [g]
      ring
    have hgcont : ContinuousOn g (Set.uIcc 0 x) := by
      apply (continuousOn_const.mul Real.continuous_arcsin.continuousOn).div
        (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn
      exact fun t ht ↦ (Real.sqrt_pos.2 (hsq ht)).ne'
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hgcont.intervalIntegrable
  rw [hg] at hi
  convert hi.mul_left 2 using 1
  funext k
  dsimp [f]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  have hch := Nat.add_choose_mul_factorial_mul_factorial (k + 1) (k + 1)
  rw [show k + 1 + (k + 1) = 2 * k + 2 by omega, Nat.factorial_succ k] at hch
  have hc : (Nat.choose (2 * k + 2) (k + 1) : ℝ) *
      ((k + 1) * k.factorial) * ((k + 1) * k.factorial) = (2 * k + 2).factorial := by
    exact_mod_cast hch
  dsimp [coeff, c]
  rw [mul_pow, show 2 * (k + 1) = 2 * k + 2 by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, zero_pow (by omega :
    2 * k + 1 + 1 ≠ 0), sub_zero]
  have hcn : (Nat.choose (2 * k + 2) (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k + 1 ≤ 2 * k + 2)).ne'
  rw [← hc]
  field_simp
  ring

-- Evaluate the unweighted series using Binet's formula at the two golden roots.
public lemma hasSum_even_odd :
    HasSum (fun k : ℕ ↦ ((k.factorial ^ 2 : ℕ) : ℝ) * Nat.fib (2 * k + 2) /
      (2 * k + 2).factorial) (8 * √5 / 250 * π ^ 2) ∧
    HasSum (fun k : ℕ ↦ ((k.factorial ^ 2 : ℕ) : ℝ) * Nat.fib (2 * k + 1) /
      (2 * k + 2).factorial) ((25 - 4 * √5) / 250 * π ^ 2) := by
  have hs : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hp : arcsin (φ / 2) = 3 * π / 10 := by
    rw [show φ / 2 = cos (π / 5) by rw [cos_pi_div_five]; unfold goldenRatio; ring,
      ← sin_pi_div_two_sub, arcsin_sin] <;> linarith [Real.pi_pos]
  have hq : arcsin (-ψ / 2) = π / 10 := by
    have hcos : -ψ / 2 = cos (2 * (π / 5)) := by
      rw [cos_two_mul, cos_pi_div_five]
      unfold goldenConj
      nlinarith
    rw [hcos, ← sin_pi_div_two_sub, arcsin_sin] <;> linarith [Real.pi_pos]
  have hφ := hasSum_arcsin_sq (x := φ / 2) (by linarith [goldenRatio_pos])
    (by linarith [goldenRatio_lt_two])
  have hψ := hasSum_arcsin_sq (x := -ψ / 2) (by linarith [goldenConj_neg])
    (by linarith [neg_one_lt_goldenConj])
  rw [hp, show 2 * (φ / 2) = φ by ring] at hφ
  rw [hq, show 2 * (-ψ / 2) = -ψ by ring] at hψ
  have heven (k : ℕ) : Even (2 * k + 2) := ⟨k + 1, by omega⟩
  simp only [(heven _).neg_pow] at hψ
  constructor
  · convert (hφ.sub hψ).div_const (√5) using 1
    · funext k
      simp only [coeff, Nat.cast_pow, div_mul_eq_mul_div]
      rw [coe_fib_eq]
      ring
    · field_simp
      nlinarith only [hs]
  · convert ((hφ.mul_right (-ψ)).sub (hψ.mul_right (-φ))).div_const (√5) using 1
    · funext k
      simp only [coeff, Nat.cast_pow, div_mul_eq_mul_div]
      rw [coe_fib_eq, pow_succ φ (2 * k + 1), pow_succ ψ (2 * k + 1)]
      simp only [mul_assoc, mul_neg, goldenRatio_mul_goldenConj, goldenConj_mul_goldenRatio,
        neg_neg]
      ring
    · unfold goldenConj goldenRatio
      field_simp
      nlinarith only [hs]

end pi_sq_eq_fibonacci_central_series

/-- **Two Fibonacci series for $\pi^2$.** Writing $F_m$ for the Fibonacci numbers ($F_0 = 0$,
$F_1 = 1$),

$$\pi^2 = \frac{250}{8\sqrt{5}} \sum_{k=0}^{\infty} \frac{(k!)^2 \, F_{2k+2}}{(2k+2)!}
\quad \text{and} \quad
\pi^2 = \frac{250}{25 - 4\sqrt{5}} \sum_{k=0}^{\infty} \frac{(k!)^2 \, F_{2k+1}}{(2k+2)!}.$$

These are identities (2.3) and (2.4) of the paper, the case $n = 1$ of its Theorem 2.1.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.2 (`fq-2024-tonien10292023-lem-2.2`). -/
public theorem pi_sq_eq_fibonacci_central_series :
    Real.pi ^ 2 = 250 / (8 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 2) : ℝ) / ((2 * k + 2).factorial : ℝ) ∧
      Real.pi ^ 2 = 250 / (25 - 4 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 1) : ℝ) / ((2 * k + 2).factorial : ℝ) := by
  obtain ⟨heven, hodd⟩ := pi_sq_eq_fibonacci_central_series.hasSum_even_odd
  have hs : √(5 : ℝ) ≠ 0 := by positivity
  have hodd_denom : 25 - 4 * √(5 : ℝ) ≠ 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  constructor
  · rw [heven.tsum_eq]
    field_simp
  · rw [hodd.tsum_eq]
    field_simp

end MetaMathlibExt
