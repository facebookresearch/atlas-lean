/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Bound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open intervalIntegral MeasureTheory Real

/-- Beta integral at natural exponents: `∫₀¹ xᵃ(1-x)ᵇ = a!·b!/(a+b+1)!`. -/
private theorem beta_nat (a b : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ b
      = (a.factorial * b.factorial : ℝ) / (a + b + 1).factorial := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero]
    rw [integral_pow, zero_pow (Nat.add_one_ne_zero a), one_pow, Nat.factorial_succ]
    push_cast
    field_simp
    norm_num
  | succ b IH =>
    have key : ∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ (b + 1)
        = ((b : ℝ) + 1) / ((a : ℝ) + 1) * ∫ x in (0:ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun x : ℝ => (1 - x) ^ (b + 1))
            (-((b : ℝ) + 1) * (1 - x) ^ b) x := by
        intro x _
        have h0 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
          simpa using (hasDerivAt_id x).const_sub 1
        have := h0.pow (b + 1)
        simp only [Nat.add_sub_cancel] at this
        convert this using 1
        push_cast; ring
      have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1,
          HasDerivAt (fun x : ℝ => x ^ (a + 1) / ((a : ℝ) + 1)) (x ^ a) x := by
        intro x _
        have := (hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)
        simp only [Nat.add_sub_cancel] at this
        convert this using 1
        push_cast; field_simp
      have hu' : IntervalIntegrable (fun x : ℝ => -((b : ℝ) + 1) * (1 - x) ^ b) volume 0 1 := by
        apply Continuous.intervalIntegrable; fun_prop
      have hv' : IntervalIntegrable (fun x : ℝ => x ^ a) volume 0 1 := by
        apply Continuous.intervalIntegrable; fun_prop
      have ibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
      have comm1 : (∫ x in (0:ℝ)..1, x ^ a * (1 - x) ^ (b + 1))
          = ∫ x in (0:ℝ)..1, (1 - x) ^ (b + 1) * x ^ a := by
        simp_rw [mul_comm]
      have reshape : ∀ x : ℝ, (-((b : ℝ) + 1) * (1 - x) ^ b) * (x ^ (a + 1) / ((a : ℝ) + 1))
          = (-((b : ℝ) + 1) / ((a : ℝ) + 1)) * (x ^ (a + 1) * (1 - x) ^ b) := fun x => by ring
      rw [comm1, ibp]
      simp only [reshape]
      rw [intervalIntegral.integral_const_mul]
      rw [show (1 - (1:ℝ)) ^ (b + 1) = 0 by norm_num,
        zero_pow (Nat.add_one_ne_zero a)]
      ring
    rw [key, IH (a + 1)]
    have e1 : (a + 1) + b + 1 = a + (b + 1) + 1 := by omega
    rw [e1, Nat.factorial_succ a, Nat.factorial_succ b]
    have ha : ((a : ℝ) + 1) ≠ 0 := by positivity
    have hf : (Nat.factorial (a + (b + 1) + 1) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hfa : (Nat.factorial a : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hfb : (Nat.factorial b : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    field_simp

/-- The rational integral behind the first sum. -/
private theorem integral_sum1 :
    ∫ t in (0:ℝ)..1, (1 - t) / (t ^ 2 - t + 1) = Real.pi * Real.sqrt 3 / 9 := by
  set s : ℝ := Real.sqrt 3 with hs
  have hs2 : s ^ 2 = 3 := by rw [hs, Real.sq_sqrt]; norm_num
  have hspos : 0 < s := by rw [hs]; positivity
  set G : ℝ → ℝ := fun t => -(1/2) * Real.log (t ^ 2 - t + 1) + (1 / s) * Real.arctan
      ((2 * t - 1) / s) with hG
  have hden : ∀ t : ℝ, 0 < t ^ 2 - t + 1 := by
    intro t; nlinarith [sq_nonneg (2 * t - 1)]
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt G ((1 - t) / (t ^ 2 - t + 1)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => Real.log (t ^ 2 - t + 1))
        ((2 * t - 1) / (t ^ 2 - t + 1)) t := by
      have : HasDerivAt (fun t : ℝ => t ^ 2 - t + 1) (2 * t - 1) t := by
        have := (hasDerivAt_pow 2 t)
        simpa using ((this.sub (hasDerivAt_id t)).add_const 1)
      simpa [div_eq_mul_inv] using this.log (ne_of_gt (hden t))
    have h2 : HasDerivAt (fun t : ℝ => Real.arctan ((2 * t - 1) / s))
        ((1 / (1 + ((2 * t - 1) / s) ^ 2)) * (2 / s)) t := by
      have hin : HasDerivAt (fun t : ℝ => (2 * t - 1) / s) (2 / s) t := by
        have : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
          simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
        simpa [div_eq_mul_inv] using this.div_const s
      exact (Real.hasDerivAt_arctan _).comp t hin
    have := ((h1.const_mul (-(1/2))).add (h2.const_mul (1 / s)))
    have hd : (t ^ 2 - t + 1) ≠ 0 := ne_of_gt (hden t)
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hs2pos : (0:ℝ) < s ^ 2 + (2 * t - 1) ^ 2 := by
      nlinarith [sq_nonneg (2 * t - 1), hs2]
    have hX : (1 : ℝ) / (1 + ((2 * t - 1) / s) ^ 2) = s ^ 2 / (s ^ 2 + (2 * t - 1) ^ 2) := by
      rw [div_pow, div_eq_div_iff (by positivity) (ne_of_gt hs2pos)]
      field_simp
    have hterm : 1 / s * (1 / (1 + ((2 * t - 1) / s) ^ 2) * (2 / s))
        = 1 / (2 * (t ^ 2 - t + 1)) := by
      rw [show 1 / s * (1 / (1 + ((2 * t - 1) / s) ^ 2) * (2 / s))
            = 2 / s ^ 2 * (1 / (1 + ((2 * t - 1) / s) ^ 2)) by ring, hX]
      simp only [hs2]
      rw [div_mul_div_comm, div_eq_div_iff (by positivity)
        (ne_of_gt (mul_pos two_pos (hden t)))]
      ring
    convert this using 1
    rw [hterm]
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => (1 - t) / (t ^ 2 - t + 1)) (Set.uIcc 0 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro t _; exact ne_of_gt (hden t)
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG]
  have e1 : (1:ℝ) ^ 2 - 1 + 1 = 1 := by norm_num
  have e0 : (0:ℝ) ^ 2 - 0 + 1 = 1 := by norm_num
  rw [e1, e0]
  have a1 : Real.arctan ((2 * (1:ℝ) - 1) / s) = Real.pi / 6 := by
    rw [show (2 * (1:ℝ) - 1) / s = (Real.sqrt 3)⁻¹ by rw [hs]; ring, Real.arctan_inv_sqrt_three]
  have a0 : Real.arctan ((2 * (0:ℝ) - 1) / s) = -(Real.pi / 6) := by
    rw [show (2 * (0:ℝ) - 1) / s = -(Real.sqrt 3)⁻¹ by rw [hs]; ring, Real.arctan_neg,
      Real.arctan_inv_sqrt_three]
  rw [a1, a0, Real.log_one]
  rw [show -(1/2) * (0:ℝ) + 1 / s * (Real.pi / 6) - (-(1/2) * 0 + 1 / s * -(Real.pi / 6))
      = Real.pi / (3 * s) by ring]
  rw [div_eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt hspos)) (by norm_num : (9:ℝ) ≠ 0)]
  linear_combination (-3 * Real.pi) * hs2

/-- The rational integral behind the second sum. -/
private theorem integral_sum2 :
    ∫ t in (0:ℝ)..1, (2 / (t ^ 2 - t + 1) ^ 2 - 1 / (t ^ 2 - t + 1) - 1)
      = 1 / 3 + 2 * Real.pi / (9 * Real.sqrt 3) := by
  set s : ℝ := Real.sqrt 3 with hs
  have hs2 : s ^ 2 = 3 := by rw [hs, Real.sq_sqrt]; norm_num
  have hspos : 0 < s := by rw [hs]; positivity
  have hden : ∀ t : ℝ, 0 < t ^ 2 - t + 1 := by
    intro t; nlinarith [sq_nonneg (2 * t - 1)]
  set G : ℝ → ℝ := fun t => 2 * (2 * t - 1) / (3 * (t ^ 2 - t + 1))
      + (2 / (3 * s)) * Real.arctan ((2 * t - 1) / s) + -t with hG
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt G (2 / (t ^ 2 - t + 1) ^ 2 - 1 / (t ^ 2 - t + 1) - 1) t := by
    intro t _
    have hd : (t ^ 2 - t + 1) ≠ 0 := ne_of_gt (hden t)
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hf : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).sub_const 1
    have hnum : HasDerivAt (fun t : ℝ => 2 * (2 * t - 1)) 4 t := by
      have := hf.const_mul (2:ℝ); convert this using 1; ring
    have hden3 : HasDerivAt (fun t : ℝ => 3 * (t ^ 2 - t + 1)) (3 * (2 * t - 1)) t := by
      have hgD : HasDerivAt (fun t : ℝ => t ^ 2 - t + 1) (2 * t - 1) t := by
        have := (hasDerivAt_pow 2 t)
        simpa using ((this.sub (hasDerivAt_id t)).add_const 1)
      exact hgD.const_mul 3
    have hne3 : (3 * (t ^ 2 - t + 1) : ℝ) ≠ 0 := by positivity
    have hp1 := hnum.div hden3 hne3
    have hp2 : HasDerivAt (fun t : ℝ => (2 / (3 * s)) * Real.arctan ((2 * t - 1) / s))
        ((2 / (3 * s)) * ((1 / (1 + ((2 * t - 1) / s) ^ 2)) * (2 / s))) t := by
      have hin : HasDerivAt (fun t : ℝ => (2 * t - 1) / s) (2 / s) t := by
        simpa [div_eq_mul_inv] using hf.div_const s
      exact ((Real.hasDerivAt_arctan _).comp t hin).const_mul (2 / (3 * s))
    have hp3 : HasDerivAt (fun t : ℝ => -t) (-1) t := by
      simpa using (hasDerivAt_id t).const_mul (-1 : ℝ)
    have := (hp1.add hp2).add hp3
    have hs2pos : (0:ℝ) < s ^ 2 + (2 * t - 1) ^ 2 := by
      nlinarith [sq_nonneg (2 * t - 1), hs2]
    have hX : (1 : ℝ) / (1 + ((2 * t - 1) / s) ^ 2) = s ^ 2 / (s ^ 2 + (2 * t - 1) ^ 2) := by
      rw [div_pow, div_eq_div_iff (by positivity) (ne_of_gt hs2pos)]
      field_simp
    have harc : (2 / (3 * s)) * ((1 / (1 + ((2 * t - 1) / s) ^ 2)) * (2 / s))
        = 1 / (3 * (t ^ 2 - t + 1)) := by
      rw [show (2 / (3 * s)) * ((1 / (1 + ((2 * t - 1) / s) ^ 2)) * (2 / s))
            = (4 / (3 * s ^ 2)) * (1 / (1 + ((2 * t - 1) / s) ^ 2)) by ring, hX]
      simp only [hs2]
      rw [div_mul_div_comm, div_eq_div_iff (by positivity)
        (ne_of_gt (mul_pos (by norm_num) (hden t)))]
      ring
    convert this using 1
    rw [harc]
    field_simp
    ring
  have hcont : ContinuousOn (fun t : ℝ => 2 / (t ^ 2 - t + 1) ^ 2 - 1 / (t ^ 2 - t + 1) - 1)
      (Set.uIcc 0 1) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) (by fun_prop)
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t _; exact pow_ne_zero 2 (ne_of_gt (hden t))
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t _; exact ne_of_gt (hden t)
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [hG]
  have e1 : (1:ℝ) ^ 2 - 1 + 1 = 1 := by norm_num
  have e0 : (0:ℝ) ^ 2 - 0 + 1 = 1 := by norm_num
  rw [e1, e0]
  have a1 : Real.arctan ((2 * (1:ℝ) - 1) / s) = Real.pi / 6 := by
    rw [show (2 * (1:ℝ) - 1) / s = (Real.sqrt 3)⁻¹ by rw [hs]; ring, Real.arctan_inv_sqrt_three]
  have a0 : Real.arctan ((2 * (0:ℝ) - 1) / s) = -(Real.pi / 6) := by
    rw [show (2 * (0:ℝ) - 1) / s = -(Real.sqrt 3)⁻¹ by rw [hs]; ring, Real.arctan_neg,
      Real.arctan_inv_sqrt_three]
  rw [a1, a0]
  ring

/-- Alternating Basel sum: `∑ₙ (-1)ⁿ/(n+1)² = π²/12`. -/
private theorem altZeta : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2)
    (Real.pi ^ 2 / 12) := by
  have hg : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using h
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2 - (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2 with hf
  have heven : HasSum (fun k : ℕ => f (2 * k)) 0 := by
    have hz : (fun k : ℕ => f (2 * k)) = fun _ => (0 : ℝ) := by
      funext k
      simp only [hf, pow_mul, neg_one_sq, one_pow]
      ring
    rw [hz]; exact hasSum_zero
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) (Real.pi ^ 2 / 12) := by
    have hval : (fun k : ℕ => f (2 * k + 1)) = fun k : ℕ => (1 / 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
      funext k
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      simp only [hf]
      have e : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * ((k : ℝ) + 1) := by push_cast; ring
      rw [e]
      have hneg : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_add, pow_mul]; simp
      rw [hneg]
      field_simp
      ring
    rw [hval]
    have := hg.mul_left (1 / 2)
    convert this using 1
    ring
  have hh := heven.even_add_odd hodd
  have hsub := hg.sub hh
  convert hsub using 1
  · funext n; simp only [hf]; ring
  · ring

/-- Power-series identity: `∑ₙ (-1)ⁿ(tⁿ - t^(3n+2))/(n+1) = -log(t²-t+1)/t` on `(0,1)`. -/
private theorem ptwise_log (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (t ^ n - t ^ (3 * n + 2)) / ((n : ℝ) + 1))
      (-Real.log (t ^ 2 - t + 1) / t) := by
  have habs1 : |(-t : ℝ)| < 1 := by rw [abs_neg, abs_of_pos ht0]; exact ht1
  have habs3 : |(-(t ^ 3) : ℝ)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity)]
    calc t ^ 3 ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
      _ = t := pow_one t
      _ < 1 := ht1
  have hbase1 := (hasSum_pow_div_log_of_abs_lt_one habs1).mul_left (-(1 / t))
  have hbase3 := (hasSum_pow_div_log_of_abs_lt_one habs3).mul_left (-(1 / t))
  have hne : t ≠ 0 := ne_of_gt ht0
  have hL1 : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * t ^ n / ((n : ℝ) + 1)) (Real.log (1 + t) / t) := by
    convert hbase1 using 2 with n
    · rw [neg_pow t (n + 1), pow_succ t n, pow_succ (-1 : ℝ) n]; field_simp
    · rw [show (1 : ℝ) - -t = 1 + t by ring]; field_simp
  have hL3 : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * t ^ (3 * n + 2) / ((n : ℝ) + 1))
      (Real.log (1 + t ^ 3) / t) := by
    convert hbase3 using 2 with n
    · rw [neg_pow (t ^ 3) (n + 1), ← pow_mul, show 3 * (n + 1) = (3 * n + 2) + 1 by ring,
        pow_succ t (3 * n + 2), pow_succ (-1 : ℝ) n]
      field_simp
    · rw [show (1 : ℝ) - -(t ^ 3) = 1 + t ^ 3 by ring]; field_simp
  have hsub := hL1.sub hL3
  have hpos1 : (0:ℝ) < 1 + t := by linarith
  have hpos3 : (0:ℝ) < 1 + t ^ 3 := by positivity
  have hposD : (0:ℝ) < t ^ 2 - t + 1 := by nlinarith [sq_nonneg (2 * t - 1)]
  convert hsub using 2 with n
  · ring
  · rw [← sub_div, ← Real.log_div hpos1.ne' hpos3.ne']
    rw [show (1 + t) / (1 + t ^ 3) = (t ^ 2 - t + 1)⁻¹ by
      rw [inv_eq_one_div, div_eq_div_iff hpos3.ne' hposD.ne']; ring]
    rw [Real.log_inv]

/-- The log integral behind the third sum. -/
private theorem integral_sum3 : ∫ t in (0:ℝ)..1, -Real.log (t ^ 2 - t + 1) / t = Real.pi ^ 2 /
    18 := by
  have hInt : HasSum
      (fun n : ℕ => ∫ t in (0:ℝ)..1, (-1 : ℝ) ^ n * (t ^ n - t ^ (3 * n + 2)) / ((n : ℝ) + 1))
      (∫ t in (0:ℝ)..1, -Real.log (t ^ 2 - t + 1) / t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun (n : ℕ) (t : ℝ) => 2 * t ^ n * (1 - t))
    · intro n; apply Continuous.aestronglyMeasurable; fun_prop
    · intro n
      refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht0 := ht.1; have ht1 := ht.2
      have hnum : 0 ≤ t ^ n - t ^ (3 * n + 2) := by
        have : t ^ (3 * n + 2) ≤ t ^ n := by
          rw [show 3 * n + 2 = n + (2 * n + 2) by ring, pow_add]
          calc t ^ n * t ^ (2 * n + 2) ≤ t ^ n * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ ht0.le ht1) (pow_nonneg ht0.le _)
            _ = t ^ n := mul_one _
        linarith
      rw [Real.norm_eq_abs, show (-1 : ℝ) ^ n * (t ^ n - t ^ (3 * n + 2)) / ((n : ℝ) + 1)
          = (-1 : ℝ) ^ n * ((t ^ n - t ^ (3 * n + 2)) / ((n : ℝ) + 1)) by ring,
        abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (div_nonneg hnum (by positivity))]
      rw [div_le_iff₀ (by positivity)]
      have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ t - 1 by linarith) (2 * n + 2)
      rw [show (1 : ℝ) + (t - 1) = t by ring] at hb
      have h2 : t ^ (3 * n + 2) = t ^ n * t ^ (2 * n + 2) := by rw [← pow_add]; ring_nf
      have hpn : (0:ℝ) ≤ t ^ n := pow_nonneg ht0.le _
      push_cast at hb ⊢
      nlinarith [mul_le_mul_of_nonneg_left hb hpn, hpn, h2]
    · refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      rcases lt_or_eq_of_le ht.2 with h1 | h1
      · exact (((hasSum_geometric_of_lt_one ht.1.le h1).summable).mul_left
          (2 * (1 - t))).congr (fun n => by ring)
      · rw [h1]; simp
    · have hEq : Set.EqOn (fun t : ℝ => ∑' n : ℕ, 2 * t ^ n * (1 - t)) (fun _ => (2:ℝ))
          (Set.Ioo 0 1) := by
        intro t ht
        change ∑' n : ℕ, 2 * t ^ n * (1 - t) = 2
        rw [show (fun n : ℕ => 2 * t ^ n * (1 - t)) = fun n => 2 * (1 - t) * t ^ n by
          funext n; ring, tsum_mul_left, tsum_geometric_of_lt_one ht.1.le ht.2]
        have hne : (1 - t : ℝ) ≠ 0 := by have := ht.2; linarith
        field_simp
      exact (intervalIntegrable_const (c := (2:ℝ))).congr_uIoo
        (by rw [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hEq.symm)
    · refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      rcases lt_or_eq_of_le ht.2 with h1 | h1
      · exact ptwise_log t ht.1 h1
      · rw [h1, show (fun n : ℕ => (-1 : ℝ) ^ n * ((1:ℝ) ^ n - (1:ℝ) ^ (3 * n + 2)) / ((n : ℝ) + 1))
            = fun _ => (0:ℝ) by funext n; simp,
          show -Real.log ((1:ℝ) ^ 2 - 1 + 1) / 1 = 0 by
            rw [show (1:ℝ) ^ 2 - 1 + 1 = 1 by norm_num, Real.log_one]; norm_num]
        exact hasSum_zero
  have hfun : (fun n : ℕ => ∫ t in (0:ℝ)..1, (-1 : ℝ) ^ n * (t ^ n - t ^ (3 * n + 2)) /
      ((n : ℝ) + 1))
      = fun n : ℕ => (2 / 3) * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) := by
    funext n
    rw [show (fun t : ℝ => (-1 : ℝ) ^ n * (t ^ n - t ^ (3 * n + 2)) / ((n : ℝ) + 1))
        = fun t : ℝ => ((-1 : ℝ) ^ n / ((n : ℝ) + 1)) * (t ^ n - t ^ (3 * n + 2)) by
      funext t; ring]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop),
      integral_pow, integral_pow]
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [zero_pow (by positivity), zero_pow (by positivity)]
    push_cast
    field_simp
    ring
  have haltz : HasSum (fun n : ℕ => (2 / 3) * ((-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2))
      (Real.pi ^ 2 / 18) := by
    have := altZeta.mul_left (2 / 3)
    convert this using 1
    ring
  rw [hfun] at hInt
  exact hInt.unique haltz

/-- First reciprocal central binomial sum. -/
private theorem hasSum_sum1 :
    HasSum (fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
      (Real.pi * Real.sqrt 3 / 9) := by
  have hInt : HasSum (fun m : ℕ => ∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ (m + 1))
      (∫ t in (0:ℝ)..1, (1 - t) / (t ^ 2 - t + 1)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun (m : ℕ) (_ : ℝ) => (1 / 4 : ℝ) ^ m)
    · intro n; apply Continuous.aestronglyMeasurable; fun_prop
    · intro n
      refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hnn : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht.1.le h1t
      have hprod : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (pow_nonneg h1t _))]
      calc t ^ n * (1 - t) ^ (n + 1) = (t * (1 - t)) ^ n * (1 - t) := by rw [mul_pow]; ring
        _ ≤ (1 / 4 : ℝ) ^ n * 1 :=
            mul_le_mul (pow_le_pow_left₀ hnn hprod n) (by linarith [ht.1.le]) h1t (by positivity)
        _ = (1 / 4 : ℝ) ^ n := by ring
    · exact ae_of_all _ fun t _ => summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hnn : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht.1.le h1t
      have hr1 : t * (1 - t) < 1 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have hg := (hasSum_geometric_of_lt_one hnn hr1).mul_left (1 - t)
      have hval : (1 - t) / (t ^ 2 - t + 1) = (1 - t) * (1 - t * (1 - t))⁻¹ := by
        rw [show (1:ℝ) - t * (1 - t) = t ^ 2 - t + 1 by ring, div_eq_mul_inv]
      have hfe : (fun n : ℕ => t ^ n * (1 - t) ^ (n + 1))
          = fun n : ℕ => (1 - t) * (t * (1 - t)) ^ n := by
        funext n; rw [mul_pow]; ring
      rw [hval, hfe]
      exact hg
  have hfun : (fun m : ℕ => ∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ (m + 1))
      = fun m : ℕ => 1 / (((m + 1 : ℕ) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)) := by
    funext m
    rw [beta_nat m (m + 1)]
    have hle : m + 1 ≤ 2 * (m + 1) := by omega
    have hsub : 2 * (m + 1) - (m + 1) = m + 1 := by omega
    have hC := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at hC
    have e : m + (m + 1) + 1 = 2 * (m + 1) := by omega
    rw [e]
    have hCr : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
        * (Nat.factorial (m + 1)) * (Nat.factorial (m + 1)) = (Nat.factorial (2 * (m + 1))) := by
      exact_mod_cast hC
    rw [← hCr, Nat.factorial_succ m]
    have hCpos : 0 < Nat.choose (2 * (m + 1)) (m + 1) := Nat.choose_pos hle
    have h1 : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
    have h2 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h4 : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [integral_sum1] at hInt
  rw [hfun] at hInt
  exact hInt

/-- Second reciprocal central binomial sum. -/
private theorem hasSum_sum2 :
    HasSum (fun m : ℕ => 1 / (Nat.choose (2 * (m + 1)) (m + 1) : ℝ))
      (1 / 3 + 2 * Real.pi / (9 * Real.sqrt 3)) := by
  have hInt : HasSum
      (fun m : ℕ => ∫ t in (0:ℝ)..1, (2 * (m : ℝ) + 3) * t ^ (m + 1) * (1 - t) ^ (m + 1))
      (∫ t in (0:ℝ)..1, (2 / (t ^ 2 - t + 1) ^ 2 - 1 / (t ^ 2 - t + 1) - 1)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun (m : ℕ) (_ : ℝ) => (2 * (m : ℝ) + 3) * (1 / 4 : ℝ) ^ (m + 1))
    · intro n; apply Continuous.aestronglyMeasurable; fun_prop
    · intro n
      refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hnn : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht.1.le h1t
      have hprod : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have hcnn : (0:ℝ) ≤ 2 * (n : ℝ) + 3 := by positivity
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg hcnn (pow_nonneg ht.1.le _)) (pow_nonneg h1t _))]
      have hkey : t ^ (n + 1) * (1 - t) ^ (n + 1) ≤ (1 / 4 : ℝ) ^ (n + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hnn hprod (n + 1)
      calc (2 * (n : ℝ) + 3) * t ^ (n + 1) * (1 - t) ^ (n + 1)
          = (2 * (n : ℝ) + 3) * (t ^ (n + 1) * (1 - t) ^ (n + 1)) := by ring
        _ ≤ (2 * (n : ℝ) + 3) * (1 / 4 : ℝ) ^ (n + 1) := by
            apply mul_le_mul_of_nonneg_left hkey hcnn
    · refine ae_of_all _ fun t _ => ?_
      have hs1 : Summable (fun m : ℕ => (m : ℝ) * (1 / 4 : ℝ) ^ m) := by
        have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (by rw [Real.norm_eq_abs]; norm_num : ‖(1 / 4 : ℝ)‖ < 1)
        simpa using this
      have hs2 : Summable (fun m : ℕ => (1 / 4 : ℝ) ^ m) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      refine ((hs1.mul_left (2 * (1 / 4 : ℝ))).add (hs2.mul_left (3 * (1 / 4 : ℝ)))).congr
        (fun m => ?_)
      ring
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hu0 : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht.1.le h1t
      have hu1 : t * (1 - t) < 1 := by nlinarith [sq_nonneg (t - 1 / 2)]
      have hnorm : ‖t * (1 - t)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hu0]; exact hu1
      have hd : (t ^ 2 - t + 1 : ℝ) ≠ 0 := by nlinarith [sq_nonneg (2 * t - 1)]
      have hg1 := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
      have hg2 := hasSum_geometric_of_lt_one hu0 hu1
      have hcomb := (hg1.mul_left (2 * (t * (1 - t)))).add (hg2.mul_left (3 * (t * (1 - t))))
      have hfe : (fun m : ℕ => (2 * (m : ℝ) + 3) * t ^ (m + 1) * (1 - t) ^ (m + 1))
          = fun m : ℕ => 2 * (t * (1 - t)) * ((m : ℝ) * (t * (1 - t)) ^ m)
              + 3 * (t * (1 - t)) * (t * (1 - t)) ^ m := by
        funext m; rw [mul_pow]; ring
      have hval : 2 * (t * (1 - t)) * ((t * (1 - t)) / (1 - t * (1 - t)) ^ 2)
            + 3 * (t * (1 - t)) * (1 - t * (1 - t))⁻¹
          = 2 / (t ^ 2 - t + 1) ^ 2 - 1 / (t ^ 2 - t + 1) - 1 := by
        set D := t ^ 2 - t + 1 with hDdef
        have hDne : D ≠ 0 := by rw [hDdef]; nlinarith [sq_nonneg (2 * t - 1)]
        have h1u : (1:ℝ) - t * (1 - t) = D := by rw [hDdef]; ring
        have hu : t * (1 - t) = 1 - D := by rw [hDdef]; ring
        simp only [h1u]
        simp only [hu]
        field_simp
        ring
      rw [hfe, ← hval]
      exact hcomb
  have hfun : (fun m : ℕ => ∫ t in (0:ℝ)..1, (2 * (m : ℝ) + 3) * t ^ (m + 1) * (1 - t) ^ (m + 1))
      = fun m : ℕ => 1 / (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) := by
    funext m
    have hc : ∀ t : ℝ, (2 * (m : ℝ) + 3) * t ^ (m + 1) * (1 - t) ^ (m + 1)
        = (2 * (m : ℝ) + 3) * (t ^ (m + 1) * (1 - t) ^ (m + 1)) := fun t => by ring
    simp_rw [hc]
    rw [intervalIntegral.integral_const_mul, beta_nat (m + 1) (m + 1)]
    have hle : m + 1 ≤ 2 * (m + 1) := by omega
    have hsub : 2 * (m + 1) - (m + 1) = m + 1 := by omega
    have hC := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at hC
    have hCr : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
        * (Nat.factorial (m + 1)) * (Nat.factorial (m + 1)) = (Nat.factorial (2 * (m + 1))) := by
      exact_mod_cast hC
    have e : (m + 1) + (m + 1) + 1 = 2 * (m + 1) + 1 := by omega
    rw [e, Nat.factorial_succ (2 * (m + 1))]
    have hCpos : 0 < Nat.choose (2 * (m + 1)) (m + 1) := Nat.choose_pos hle
    have h1 : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
    have h2 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    rw [← hCr]
    field_simp
    ring
  rw [integral_sum2] at hInt
  rw [hfun] at hInt
  exact hInt

/-- Third reciprocal central binomial sum. -/
private theorem hasSum_sum3 :
    HasSum (fun m : ℕ => 1 / ((((m + 1 : ℕ) : ℝ) ^ 2) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
      (Real.pi ^ 2 / 18) := by
  have hInt : HasSum (fun m : ℕ => ∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ (m + 1) / ((m : ℝ) + 1))
      (∫ t in (0:ℝ)..1, -Real.log (t ^ 2 - t + 1) / t) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (bound := fun (m : ℕ) (_ : ℝ) => (1 / 4 : ℝ) ^ m)
    · intro n; apply Continuous.aestronglyMeasurable; fun_prop
    · intro n
      refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hnn : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht.1.le h1t
      have hprod : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (pow_nonneg h1t _))
          (by positivity))]
      rw [div_le_iff₀ (by positivity)]
      have hle : t ^ n * (1 - t) ^ (n + 1) ≤ (1 / 4 : ℝ) ^ n := by
        calc t ^ n * (1 - t) ^ (n + 1) = (t * (1 - t)) ^ n * (1 - t) := by rw [mul_pow]; ring
          _ ≤ (1 / 4 : ℝ) ^ n * 1 :=
              mul_le_mul (pow_le_pow_left₀ hnn hprod n) (by linarith [ht.1.le]) h1t (by positivity)
          _ = (1 / 4 : ℝ) ^ n := by ring
      nlinarith [hle, pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) n, Nat.cast_nonneg (α := ℝ) n]
    · exact ae_of_all _ fun t _ => summable_geometric_of_lt_one (by norm_num) (by norm_num)
    · exact intervalIntegrable_const
    · refine ae_of_all _ fun t ht => ?_
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      have ht0 := ht.1
      have h1t : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
      have hu0 : (0:ℝ) ≤ t * (1 - t) := mul_nonneg ht0.le h1t
      have huabs : |t * (1 - t)| < 1 := by
        rw [abs_of_nonneg hu0]; nlinarith [sq_nonneg (2 * t - 1)]
      have hne : t ≠ 0 := ne_of_gt ht0
      have hg := (hasSum_pow_div_log_of_abs_lt_one huabs).mul_left (1 / t)
      have hval : 1 / t * -Real.log (1 - t * (1 - t)) = -Real.log (t ^ 2 - t + 1) / t := by
        rw [show (1:ℝ) - t * (1 - t) = t ^ 2 - t + 1 by ring]; ring
      have hfe : (fun m : ℕ => t ^ m * (1 - t) ^ (m + 1) / ((m : ℝ) + 1))
          = fun m : ℕ => 1 / t * ((t * (1 - t)) ^ (m + 1) / ((m : ℝ) + 1)) := by
        funext m
        rw [mul_pow]
        field_simp
        ring
      rw [hval] at hg
      rw [hfe]
      exact hg
  have hfun : (fun m : ℕ => ∫ t in (0:ℝ)..1, t ^ m * (1 - t) ^ (m + 1) / ((m : ℝ) + 1))
      = fun m : ℕ => 1 / ((((m + 1 : ℕ) : ℝ) ^ 2) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)) := by
    funext m
    rw [show (fun t : ℝ => t ^ m * (1 - t) ^ (m + 1) / ((m : ℝ) + 1))
        = fun t : ℝ => (1 / ((m : ℝ) + 1)) * (t ^ m * (1 - t) ^ (m + 1)) by funext t; ring]
    rw [intervalIntegral.integral_const_mul, beta_nat m (m + 1)]
    have hle : m + 1 ≤ 2 * (m + 1) := by omega
    have hsub : 2 * (m + 1) - (m + 1) = m + 1 := by omega
    have hC := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at hC
    have e : m + (m + 1) + 1 = 2 * (m + 1) := by omega
    rw [e]
    have hCr : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)
        * (Nat.factorial (m + 1)) * (Nat.factorial (m + 1)) = (Nat.factorial (2 * (m + 1))) := by
      exact_mod_cast hC
    rw [← hCr, Nat.factorial_succ m]
    have hCpos : 0 < Nat.choose (2 * (m + 1)) (m + 1) := Nat.choose_pos hle
    have h1 : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) ≠ 0 := by exact_mod_cast hCpos.ne'
    have h2 : (Nat.factorial (m + 1) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h3 : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h4 : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [integral_sum3] at hInt
  rw [hfun] at hInt
  exact hInt

section
namespace MetaMathlibExt

/-! # Reciprocal central binomial sums evaluating to pi
-/

/--
**Sums of reciprocals of central binomial coefficients.** The following three series converge
absolutely, with the stated sums:
$$\sum_{n=1}^{\infty} \frac{1}{n \binom{2n}{n}} = \frac{\pi \sqrt{3}}{9},$$
$$\sum_{n=1}^{\infty} \frac{1}{\binom{2n}{n}} = \frac{1}{3} + \frac{2\pi}{9\sqrt{3}},$$
$$\sum_{n=1}^{\infty} \frac{1}{n^2 \binom{2n}{n}} = \frac{\pi^2}{18}.$$

Proves `Wanted` entry `reciprocal_central_binomial_sums`.

Source: B. Sury, Tianming Wang, and Feng-Zhen Zhao, "Identities Involving
Reciprocals of Binomial Coefficients," Journal of Integer Sequences 7 (2004),
Article 04.2.8, Corollary, lines 392–398,
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Sury/sury99.tex>.
-/
theorem reciprocal_central_binomial_sums :
    HasSum
        (fun m : ℕ =>
          1 / (((m + 1 : ℕ) : ℝ) * (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
        (Real.pi * Real.sqrt 3 / 9) ∧
      HasSum
        (fun m : ℕ => 1 / (Nat.choose (2 * (m + 1)) (m + 1) : ℝ))
        (1 / 3 + 2 * Real.pi / (9 * Real.sqrt 3)) ∧
      HasSum
        (fun m : ℕ =>
          1 /
            ((((m + 1 : ℕ) : ℝ) ^ 2) *
              (Nat.choose (2 * (m + 1)) (m + 1) : ℝ)))
        (Real.pi ^ 2 / 18) :=
  ⟨hasSum_sum1, hasSum_sum2, hasSum_sum3⟩

end MetaMathlibExt
