/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FibonacciPiSquared
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# Fibonacci series for π² with polynomial weights

Tonien's two factorial series evaluate to multiples of π². Their initial values follow
from an integral of Lehmer's arcsine series, and their weights satisfy a difference recurrence.
-/

open Polynomial Real
open scoped goldenRatio

namespace MetaMathlibExt
namespace pi_sq_eq_fibonacci_factorial_series

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

/-- Evaluate the unweighted series using Binet's formula at the two golden roots. -/
private lemma base_sums :
    HasSum (fun k ↦ coeff k * Nat.fib (2 * k + 2)) (8 * √5 / 250 * π ^ 2) ∧
    HasSum (fun k ↦ coeff k * Nat.fib (2 * k + 1)) ((25 - 4 * √5) / 250 * π ^ 2) := by
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
      rw [coe_fib_eq]
      ring
    · field_simp
      nlinarith only [hs]
  · convert ((hφ.mul_right (-ψ)).sub (hψ.mul_right (-φ))).div_const (√5) using 1
    · funext k
      rw [coe_fib_eq, pow_succ φ (2 * k + 1), pow_succ ψ (2 * k + 1)]
      simp only [mul_assoc, mul_neg, goldenRatio_mul_goldenConj, goldenConj_mul_goldenRatio,
        neg_neg]
      ring
    · unfold goldenConj goldenRatio
      field_simp
      nlinarith only [hs]

private noncomputable def weight (p : ℕ → ℤ[X]) (n k : ℕ) : ℝ :=
  (k.factorial : ℝ) ^ 2 * (((p n).eval (k : ℤ) : ℤ) : ℝ) / (2 * k + 2 * n).factorial

private lemma weight_step (p : ℕ → ℤ[X])
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    weight p (n + 1) k = weight p n k - weight p n (k + 1) := by
  unfold weight
  rw [hp n hn, show 2 * k + 2 * (n + 1) = (2 * k + 2 * n) + 1 + 1 by omega,
    show 2 * (k + 1) + 2 * n = (2 * k + 2 * n) + 1 + 1 by omega,
    Nat.factorial_succ (2 * k + 2 * n + 1), Nat.factorial_succ (2 * k + 2 * n),
    Nat.factorial_succ k]
  simp only [eval_sub, eval_mul, eval_add, eval_ofNat, eval_X, eval_C, eval_pow, eval_one,
    eval_comp]
  push_cast
  field_simp
  ring

private noncomputable abbrev evenFib (k : ℕ) : ℝ := Nat.fib (2 * k + 2)
private noncomputable abbrev oddFib (k : ℕ) : ℝ := Nat.fib (2 * k + 1)

/-- Summation by parts for one forward difference of the weights. -/
private lemma difference_sums {w : ℕ → ℝ} {u v : ℝ}
    (he : HasSum (fun k ↦ w k * evenFib k) u) (ho : HasSum (fun k ↦ w k * oddFib k) v) :
    HasSum (fun k ↦ (w k - w (k + 1)) * evenFib k) v ∧
      HasSum (fun k ↦ (w k - w (k + 1)) * oddFib k) (u - v + w 0) := by
  have he' := (hasSum_nat_add_iff' 1).2 he
  have ho' := (hasSum_nat_add_iff' 1).2 ho
  simp only [Finset.sum_range_one, show evenFib 0 = 1 by norm_num [evenFib],
    show oddFib 0 = 1 by norm_num [oddFib], mul_one] at he' ho'
  have heq (k : ℕ) : evenFib (k + 1) = oddFib (k + 1) + evenFib k := by
    unfold evenFib oddFib
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega, Nat.fib_add_two, Nat.cast_add]
    rw [add_comm, show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by omega]
  have hoq (k : ℕ) : oddFib (k + 1) = evenFib k + oddFib k := by
    unfold evenFib oddFib
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.fib_add_two, Nat.cast_add, add_comm]
  constructor
  · convert he.sub (he'.sub ho') using 1
    · funext k
      change _ = w k * evenFib k - (w (k + 1) * evenFib (k + 1) - _)
      rw [heq]
      ring
    · ring
  · convert ho.sub ((ho'.add ho').sub he') using 1
    · funext k
      change _ = w k * oddFib k - (w (k + 1) * oddFib (k + 1) + _ - w (k + 1) * evenFib (k + 1))
      rw [heq, hoq]
      ring
    · ring

private lemma coeff_ne_zero (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250)
    (ha1 : a 1 = (25 - 4 * √5) / 250) (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1))
    (n : ℕ) : a n ≠ 0 := by
  cases n with
  | zero =>
    rw [ha0]
    exact div_ne_zero (neg_ne_zero.mpr (by positivity)) (by norm_num)
  | succ n =>
    intro h
    rw [fibPiSquared_coeff_eq_fib a ha0 ha1 ha n] at h
    have hirr : Irrational (√5) := by simpa using (by decide : Nat.Prime 5).irrational_sqrt
    apply hirr.ne_rational (25 * Nat.fib (n + 1)) (4 * Nat.fib (n + 1) + 8 * Nat.fib n)
    push_cast
    have hf : (0 : ℝ) < Nat.fib (n + 1) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)
    apply (eq_div_iff (by positivity)).2
    linarith only [h]

end pi_sq_eq_fibonacci_factorial_series

open pi_sq_eq_fibonacci_factorial_series in
/-- **Fibonacci series for $\pi^2$ with polynomial weights.** Let $p_1, p_2, \dots$ be polynomials
with integer coefficients such that $p_1 = 1$ and, for every $n \ge 1$,
$p_{n+1}(x) = (2x + 2n + 1)(2x + 2n + 2)\, p_n(x) - (x + 1)^2 p_n(x + 1)$. Let $(a_n)_{n \ge 0}$
be real numbers with $a_0 = -8\sqrt{5}/250$, $a_1 = (25 - 4\sqrt{5})/250$ and
$a_{n+1} = a_n + a_{n-1}$ for $n \ge 1$, and let $(b_n)_{n \ge 0}$ be real numbers with
$b_0 = b_1 = 0$ and $b_{n+1} = b_n + b_{n-1} + (-1)^{n+1} p_n(0)/(2n)!$ for $n \ge 1$. Write $F_m$
for the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every $n \ge 1$,

$$\pi^2 = \frac{1}{a_{n-1}} \Bigl(b_{n-1} + (-1)^n \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+2}}{(2k+2n)!}\Bigr)$$

and

$$\pi^2 = \frac{1}{a_n} \Bigl(b_n + (-1)^{n+1} \sum_{k=0}^{\infty}
\frac{(k!)^2 \, p_n(k) \, F_{2k+1}}{(2k+2n)!}\Bigr).$$

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Theorem 2.1 (`fq-2024-tonien10292023-thm-2.1`). -/
public theorem pi_sq_eq_fibonacci_factorial_series (p : ℕ → ℤ[X]) (hp1 : p 1 = 1)
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250) (ha1 : a 1 = (25 - 4 * √5) / 250)
    (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb1 : b 1 = 0)
    (hb : ∀ n, 1 ≤ n → b (n + 1) =
      b n + b (n - 1) + (-1) ^ (n + 1) * (((p n).eval 0 : ℤ) : ℝ) / ((2 * n).factorial : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    Real.pi ^ 2 = (b (n - 1) + (-1) ^ n * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 2) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a (n - 1) ∧
      Real.pi ^ 2 = (b n + (-1) ^ (n + 1) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 1) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a n := by
  have hsign (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by rw [pow_right_comm]; simp
  have sums :
      HasSum (fun k ↦ weight p n k * evenFib k) ((-1) ^ n * (π ^ 2 * a (n - 1) - b (n - 1))) ∧
      HasSum (fun k ↦ weight p n k * oddFib k) ((-1) ^ (n + 1) * (π ^ 2 * a n - b n)) := by
    induction n, hn using Nat.le_induction with
    | base =>
      simpa [weight, coeff, evenFib, oddFib, hp1, ha0, ha1, hb0, hb1, neg_div, mul_comm] using
        base_sums
    | succ n hn ih =>
      obtain ⟨he, ho⟩ := difference_sums ih.1 ih.2
      simp_rw [weight_step p hp hn]
      refine ⟨by simpa using he, ?_⟩
      convert ho using 1
      rw [ha n hn, hb n hn]
      simp only [weight, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul, Nat.cast_zero,
        mul_zero, zero_add, pow_succ]
      linear_combination ((((p n).eval 0 : ℤ) : ℝ) / (2 * n).factorial) * hsign n
  have hne := coeff_ne_zero a ha0 ha1 ha
  have value (m j : ℕ) {s : ℝ} (hs : s = (-1) ^ m * (π ^ 2 * a j - b j)) :
      π ^ 2 = (b j + (-1) ^ m * s) / a j := by
    rw [eq_div_iff (hne j), hs]
    linear_combination -(π ^ 2 * a j - b j) * hsign m
  constructor
  · apply value n (n - 1)
    simpa only [weight, evenFib, Nat.cast_pow, div_mul_eq_mul_div] using sums.1.tsum_eq
  · apply value (n + 1) n
    simpa only [weight, oddFib, Nat.cast_pow, div_mul_eq_mul_div] using sums.2.tsum_eq

end MetaMathlibExt
