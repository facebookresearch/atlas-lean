/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatDuhamelSeries
import MathlibExt.Analysis.PDE.HeatKernelUniqueness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Volterra series for the potential-heat equation

Iteration of the Gaussian Duhamel integral constructs the potential-heat
solution. Factorial time estimates control the iterates with exponential
spatial weights.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open MathlibExt.Analysis

namespace MathlibExt.Analysis.PDE.HeatKernel

/-- A time-dependent nonnegative amplitude gives an integrated Duhamel bound,
with the same exponential spatial weight and one finite Gaussian moment. -/
theorem abs_heatDuhamel_le_time_weight {f : ℝ → ℝ → ℝ} {a : ℝ → ℝ} {T c ν t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ)) (hc : 0 ≤ c)
    (ha : ∀ s ∈ Icc 0 T, 0 ≤ a s)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, |f s x| ≤ a s * exp (c * |x|))
    (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (hi : IntervalIntegrable a volume 0 t) (x : ℝ) :
    |heatDuhamel ν f t x| ≤ (∫ s in 0..t, a s) *
      (∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)) * exp (c * |x|) := by
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have h := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := fun s => heatSolution (f s) (ν*(t-s)) x)
    (g := fun s => a s * J * exp (c * |x|)) ?_ ((hi.mul_const J).mul_const _)
  · simpa only [heatDuhamel,Real.norm_eq_abs,intervalIntegral.integral_mul_const] using h
  · filter_upwards with s
    intro hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le,hs.2.trans ht.2⟩
    have hfc : Continuous (f s) := hf.comp_continuous
      (continuous_const.prodMk continuous_id) (fun y => ⟨hsT,mem_univ y⟩)
    simpa only [Real.norm_eq_abs] using abs_heatSolution_le_exp_bound hfc (ha s hsT) hc
      (hb s hsT) (mul_le_mul_of_nonneg_left ((sub_le_self t hs.1.le).trans ht.2) hν) x

/-- Integrating a polynomial time envelope gains one power and divides by its degree. -/
theorem abs_heatDuhamel_le_time_pow {f : ℝ → ℝ → ℝ} {T A c ν t : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hA : 0 ≤ A) (hc : 0 ≤ c) (n : ℕ)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, |f s x| ≤ A * s ^ n * exp (c * |x|))
    (hν : 0 ≤ ν) (ht : t ∈ Icc 0 T) (x : ℝ) :
    |heatDuhamel ν f t x| ≤ A * t ^ (n+1) / (n+1) *
      (∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)) * exp (c * |x|) := by
  have h := abs_heatDuhamel_le_time_weight hf hc
    (fun s hs => mul_nonneg hA (pow_nonneg hs.1 n)) hb hν ht
    (by apply Continuous.intervalIntegrable; fun_prop) x
  simpa only [intervalIntegral.integral_const_mul,integral_pow,
    zero_pow (Nat.succ_ne_zero n),sub_zero,mul_div_assoc] using h

/-- The successive Volterra terms: free heat evolution, followed by repeated
Duhamel integration after multiplication by the potential. -/
noncomputable def potentialHeatIterate (ν : ℝ) (q : ℝ → ℝ → ℝ) (g : ℝ → ℝ) :
    ℕ → ℝ → ℝ → ℝ
  | 0 => fun t => heatSolution g (ν*t)
  | n+1 => heatDuhamel ν (fun s y => q s y * potentialHeatIterate ν q g n s y)

/-- The potential-heat field is the pointwise Volterra series. Convergence and
its integral equation require the bounds proved separately below. -/
noncomputable def potentialHeatSolution (ν : ℝ) (q : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∑' n : ℕ, potentialHeatIterate ν q g n t x

/-- At initial time only the freely evolved term is nonzero. -/
theorem potentialHeatIterate_initial (ν : ℝ) (q : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    potentialHeatIterate ν q g n 0 x = if n = 0 then g x else 0 := by
  cases n <;> simp [potentialHeatIterate]

/-- The Volterra field has its stated initial value. -/
@[simp] theorem potentialHeatSolution_initial (ν : ℝ) (q : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (x : ℝ) :
    potentialHeatSolution ν q g 0 x = g x := by
  simp [potentialHeatSolution,potentialHeatIterate_initial]

/-- Zero potential leaves exactly the free heat evolution. -/
@[simp] theorem potentialHeatSolution_zero_potential (ν : ℝ) (g : ℝ → ℝ) (t x : ℝ) :
    potentialHeatSolution ν (fun _ _ => 0) g t x = heatSolution g (ν*t) x := by
  have he (n : ℕ) : potentialHeatIterate ν (fun _ _ => 0) g n t x =
      if n = 0 then heatSolution g (ν*t) x else 0 := by
    cases n <;> simp [potentialHeatIterate]
  simp [potentialHeatSolution,he]

/-- Constant potential and constant initial data give the exponential-series terms. -/
theorem potentialHeatIterate_const (ν b a : ℝ) (n : ℕ) (t x : ℝ) :
    potentialHeatIterate ν (fun _ _ => b) (fun _ => a) n t x =
      a * b^n * t^n / n.factorial := by
  induction n generalizing t x with
  | zero => simp [potentialHeatIterate]
  | succ n ih =>
    simp only [potentialHeatIterate, ih]
    have he : (fun s y : ℝ => b * (a * b^n * s^n / n.factorial)) =
        fun s _ => (b * a * b^n / n.factorial) * s^n := by
      funext s y; ring
    rw [he, heatDuhamel_time_only, intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    field_simp
    ring

/-- The constructed field reproduces the exact constant-potential solution. -/
@[simp] theorem potentialHeatSolution_const (ν b a t x : ℝ) :
    potentialHeatSolution ν (fun _ _ => b) (fun _ => a) t x = a * exp (b*t) := by
  have hs : HasSum (fun n : ℕ => (b*t)^n / n.factorial) (exp (b*t)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (b*t)
  simp only [potentialHeatSolution, potentialHeatIterate_const]
  convert (hs.mul_left a).tsum_eq using 1
  congr 1
  funext n
  rw [mul_pow]
  ring

private theorem mul_strip_growth {u q : ℝ → ℝ → ℝ} {T Q : ℝ}
    (hu : HeatWholeLine.HasExpGrowthOnStrip u T) (hQ : 0 ≤ Q)
    (hq : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q) :
    HeatWholeLine.HasExpGrowthOnStrip (fun t x => q t x * u t x) T := by
  obtain ⟨M,c,hM,hc,hb⟩ := hu
  refine ⟨Q*M,c,mul_nonneg hQ hM,hc,fun t ht x => ?_⟩
  rw [abs_mul,mul_assoc]
  exact mul_le_mul (hq t ht x) (hb t ht x) (abs_nonneg _) hQ

private theorem iterate_regular {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (n : ℕ) :
    ContinuousOn (Function.uncurry (potentialHeatIterate ν q g n)) (Icc 0 T ×ˢ univ) ∧
      HeatWholeLine.HasExpGrowthOnStrip (potentialHeatIterate ν q g n) T := by
  induction n with
  | zero =>
    constructor
    · exact ((heatSolution_continuous_of_exp_growth hg hgg).comp
        ((continuous_const.mul continuous_fst).prodMk continuous_snd)).continuousOn
    · exact heatSolution_hasExpGrowthOnStrip hg hgg hν T
  | succ n ih =>
    have hc : ContinuousOn (Function.uncurry
        (fun s y => q s y * potentialHeatIterate ν q g n s y)) (Icc 0 T ×ˢ univ) := hq.mul ih.1
    have hb := mul_strip_growth ih.2 hQ hqb
    exact ⟨heatDuhamel_continuousOn hT hc hb ν, heatDuhamel_hasExpGrowthOnStrip hc hb hν hT⟩

/-- Every Volterra term is jointly continuous on the closed time strip. -/
theorem potentialHeatIterate_continuousOn {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (n : ℕ) :
    ContinuousOn (Function.uncurry (potentialHeatIterate ν q g n)) (Icc 0 T ×ˢ univ) :=
  (iterate_regular hν hT hq hQ hqb hg hgg n).1

/-- Each Volterra term retains a uniform exponential spatial bound on a finite strip. -/
theorem potentialHeatIterate_hasExpGrowthOnStrip {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) (n : ℕ) :
    HeatWholeLine.HasExpGrowthOnStrip (potentialHeatIterate ν q g n) T :=
  (iterate_regular hν hT hq hQ hqb hg hgg n).2

/-- Factorial time bounds control every Volterra term with a common spatial weight. -/
theorem abs_potentialHeatIterate_le {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q M c : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hM : 0 ≤ M) (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ M * exp (c * |x|))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
    |potentialHeatIterate ν q g n t x| ≤ M * J * (Q*J)^n * t ^ n / n.factorial * exp (c * |x|) := by
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  change |potentialHeatIterate ν q g n t x| ≤ M * J * (Q*J)^n * t ^ n / n.factorial * exp (c * |x|)
  induction n generalizing t x with
  | zero =>
    simpa only [potentialHeatIterate,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one] using
      abs_heatSolution_le_exp_bound hg hM hc hgb (mul_le_mul_of_nonneg_left ht.2 hν) x
  | succ n ih =>
    have hT := ht.1.trans ht.2
    have hcont := potentialHeatIterate_continuousOn hν hT hq hQ hqb hg ⟨M,c,hM,hc,hgb⟩ n
    let A := Q * (M * J * (Q*J)^n) / n.factorial
    have hA : 0 ≤ A := by positivity
    have hb (s : ℝ) (hs : s ∈ Icc 0 T) (y : ℝ) :
        |q s y * potentialHeatIterate ν q g n s y| ≤ A * s ^ n * exp (c * |y|) := by
      rw [abs_mul]
      calc
        _ ≤ Q * (M * J * (Q*J)^n * s ^ n / n.factorial * exp (c * |y|)) :=
          mul_le_mul (hqb s hs y) (ih hs y) (abs_nonneg _) hQ
        _ = _ := by dsimp only [A]; ring
    have h := abs_heatDuhamel_le_time_pow
      (f := fun s y => q s y * potentialHeatIterate ν q g n s y) (hq.mul hcont) hA hc n hb hν ht x
    change |heatDuhamel ν (fun s y => q s y * potentialHeatIterate ν q g n s y) t x| ≤ _
    calc
      _ ≤ A * t ^ (n+1) / (n+1) * J * exp (c * |x|) := h
      _ = _ := by
        dsimp only [A]
        rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        field_simp; ring

private theorem iterate_bound_box {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q M c R : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hM : 0 ≤ M) (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ M * exp (c * |x|))
    (n : ℕ) {t x : ℝ} (ht : t ∈ Icc 0 T) (hx : |x| ≤ R) :
    let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
    ‖potentialHeatIterate ν q g n t x‖ ≤
      (M * J * exp (c * R)) * ((Q*J*T)^n / n.factorial) := by
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  change ‖potentialHeatIterate ν q g n t x‖ ≤ (M * J * exp (c * R)) * ((Q*J*T)^n / n.factorial)
  calc
    _ ≤ M * J * (Q*J)^n * t^n / n.factorial * exp (c * |x|) := by
      simpa only [Real.norm_eq_abs] using
        abs_potentialHeatIterate_le hν hq hQ hqb hg hM hc hgb n ht x
    _ = (M * J * exp (c * |x|)) * ((Q*J*t)^n / n.factorial) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hc))
        (mul_nonneg hM hJ))
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (mul_nonneg hQ hJ) ht.1)
        (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hQ hJ)) n) (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg hQ hJ) ht.1) n) (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg hM hJ) (exp_pos _).le)

/-- The actual Volterra series is absolutely summable at every point of its finite strip. -/
theorem summable_potentialHeatIterate {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    Summable (fun n => ‖potentialHeatIterate ν q g n t x‖) := by
  obtain ⟨M,c,hM,hc,hgb⟩ := hgg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  apply ((Real.summable_pow_div_factorial (Q*J*T)).mul_left (M*J*exp (c*|x|))).of_norm_bounded
  intro n
  rw [norm_norm]
  exact iterate_bound_box hν hq hQ hqb hg hM hc hgb n ht le_rfl

/-- Summing the factorial estimates gives a quantitative exponential bound for
potential-heat evolution with bounded continuous potential. -/
theorem abs_potentialHeatSolution_le {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q M c : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hM : 0 ≤ M) (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ M * exp (c * |x|))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
    |potentialHeatSolution ν q g t x| ≤ M * J * exp (Q*J*t) * exp (c * |x|) := by
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hs : HasSum (fun n : ℕ => (Q*J*t)^n / n.factorial) (exp (Q*J*t)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (Q*J*t)
  have h := tsum_of_norm_bounded (hs.mul_left (M*J*exp (c*|x|)))
    (f := fun n => potentialHeatIterate ν q g n t x) ?_
  · change |potentialHeatSolution ν q g t x| ≤ M * J * exp (Q*J*t) * exp (c * |x|)
    simpa only [Real.norm_eq_abs,potentialHeatSolution,mul_assoc,mul_comm,mul_left_comm] using h
  · intro n
    calc
      _ ≤ M * J * (Q*J)^n * t^n / n.factorial * exp (c * |x|) := by
        simpa only [Real.norm_eq_abs] using
        abs_potentialHeatIterate_le hν hq hQ hqb hg hM hc hgb n ht x
      _ = _ := by rw [mul_pow]; ring

/-- Potential-heat evolution retains uniform exponential spatial growth. -/
theorem potentialHeatSolution_hasExpGrowthOnStrip {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    HeatWholeLine.HasExpGrowthOnStrip (potentialHeatSolution ν q g) T := by
  obtain ⟨M,c,hM,hc,hgb⟩ := hgg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  refine ⟨M*J*exp (Q*J*T),c,by positivity,hc,fun t ht x => ?_⟩
  exact (abs_potentialHeatSolution_le hν hq hQ hqb hg hM hc hgb ht x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hQ hJ))) (mul_nonneg hM hJ))
      (exp_pos _).le)

/-- Local uniform convergence of the Volterra series gives joint continuity,
including initial time, without any weighted-supremum continuity assumption. -/
theorem potentialHeatSolution_continuousOn {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) :
    ContinuousOn (Function.uncurry (potentialHeatSolution ν q g)) (Icc 0 T ×ˢ univ) := by
  obtain ⟨M,c,hM,hc,hgb⟩ := hgg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  intro p hp
  let R := |p.2|+1
  let S : Set (ℝ × ℝ) := (Icc 0 T ×ˢ univ) ∩ {z | |z.2| ≤ R}
  have hs : Summable (fun n : ℕ => (M*J*exp (c*R)) * ((Q*J*T)^n / n.factorial)) :=
    (Real.summable_pow_div_factorial (Q*J*T)).mul_left _
  have hcont : ContinuousOn (fun z : ℝ × ℝ => ∑' n, potentialHeatIterate ν q g n z.1 z.2) S := by
    apply continuousOn_tsum
      (fun n => (potentialHeatIterate_continuousOn hν hT hq hQ hqb hg ⟨M,c,hM,hc,hgb⟩ n).mono
        inter_subset_left) hs
    intro n z hz
    exact iterate_bound_box hν hq hQ hqb hg hM hc hgb n hz.1.1 hz.2
  have hpS : p ∈ S := ⟨hp,le_add_of_nonneg_right zero_le_one⟩
  have hnear : {z : ℝ × ℝ | |z.2| ≤ R} ∈ 𝓝 p := by
    have h := (continuous_snd.abs.tendsto p).eventually_lt_const (lt_add_one |p.2|)
    exact h.mono (fun z hz => hz.le)
  exact (hcont p hpS).mono_of_mem_nhdsWithin
    (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hnear))

/-- The convergent Volterra series satisfies the actual potential-heat mild equation. -/
theorem potentialHeatSolution_mild {q : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g) {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) :
    potentialHeatSolution ν q g t x = heatSolution g (ν*t) x +
      heatDuhamel ν (fun s y => q s y * potentialHeatSolution ν q g s y) t x := by
  obtain ⟨M,c,hM,hc,hgb⟩ := hgg
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  let A := fun n : ℕ => Q * (M*J) * ((Q*J*T)^n / n.factorial)
  have hA (n : ℕ) : 0 ≤ A n := by
    exact mul_nonneg (mul_nonneg hQ (mul_nonneg hM hJ))
      (div_nonneg (pow_nonneg (mul_nonneg (mul_nonneg hQ hJ) (ht.1.trans ht.2)) n)
        (Nat.cast_nonneg _))
  have hAs : Summable A := (Real.summable_pow_div_factorial (Q*J*T)).mul_left _
  have hcont (n : ℕ) : ContinuousOn (Function.uncurry
      (fun s y => q s y * potentialHeatIterate ν q g n s y)) (Icc 0 T ×ˢ univ) :=
    hq.mul (potentialHeatIterate_continuousOn hν (ht.1.trans ht.2) hq hQ hqb hg ⟨M,c,hM,hc,hgb⟩ n)
  have hb (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (y : ℝ) :
      |q s y * potentialHeatIterate ν q g n s y| ≤ A n * exp (c * |y|) := by
    have h := iterate_bound_box hν hq hQ hqb hg hM hc hgb n hs (x := y) le_rfl
    rw [Real.norm_eq_abs] at h
    rw [abs_mul]
    calc
      _ ≤ Q * ((M*J*exp (c*|y|)) * ((Q*J*T)^n / n.factorial)) :=
        mul_le_mul (hqb s hs y) h (abs_nonneg _) hQ
      _ = _ := by dsimp only [A]; ring
  have hseries := heatDuhamel_hasSum_of_exp_bound hcont hA hAs hc hb hν ht x
  have he : (fun s y => ∑' n : ℕ, q s y * potentialHeatIterate ν q g n s y) =
      fun s y => q s y * potentialHeatSolution ν q g s y := by
    funext s y
    exact tsum_mul_left
  rw [he] at hseries
  have hs := (summable_potentialHeatIterate hν hq hQ hqb hg ⟨M,c,hM,hc,hgb⟩ ht x).of_norm
  change (∑' n, potentialHeatIterate ν q g n t x) = _
  rw [hs.tsum_eq_zero_add]
  change heatSolution g (ν*t) x +
      (∑' n, heatDuhamel ν (fun s y => q s y * potentialHeatIterate ν q g n s y) t x) = _
  rw [hseries.tsum_eq]

private theorem eq_zero_of_homogeneous_mild {q u : ℝ → ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hug : HeatWholeLine.HasExpGrowthOnStrip u T)
    (he : ∀ t ∈ Icc 0 T, ∀ x, u t x = heatDuhamel ν (fun s y => q s y * u s y) t x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) : u t x = 0 := by
  obtain ⟨M,c,hM,hc,hb⟩ := hug
  let J := ∫ y : ℝ, heatKernel ℝ 1 y * exp (c * sqrt (ν*T) * |y|)
  have hJ : 0 ≤ J := integral_nonneg (fun y =>
    mul_nonneg (heatKernel_pos one_pos y).le (exp_pos _).le)
  have hbound (n : ℕ) : ∀ s ∈ Icc 0 T, ∀ y,
      |u s y| ≤ M * (Q*J)^n * s^n / n.factorial * exp (c * |y|) := by
    induction n with
    | zero => simpa only [pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one] using hb
    | succ n ih =>
      intro s hs y
      let A := Q * (M * (Q*J)^n) / n.factorial
      have hA : 0 ≤ A := by positivity
      have hb' (r : ℝ) (hr : r ∈ Icc 0 T) (z : ℝ) :
          |q r z * u r z| ≤ A * r^n * exp (c * |z|) := by
        rw [abs_mul]
        calc
          _ ≤ Q * (M * (Q*J)^n * r^n / n.factorial * exp (c * |z|)) :=
            mul_le_mul (hqb r hr z) (ih r hr z) (abs_nonneg _) hQ
          _ = _ := by dsimp only [A]; ring
      rw [he s hs y]
      calc
        _ ≤ A * s^(n+1) / (n+1) * J * exp (c * |y|) :=
          abs_heatDuhamel_le_time_pow (f := fun s y => q s y * u s y)
            (hq.mul hu) hA hc n hb' hν hs y
        _ = _ := by
          dsimp only [A]
          rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
          field_simp; ring
  have hlim : Tendsto (fun n : ℕ => M * (Q*J)^n * t^n / n.factorial * exp (c*|x|))
      atTop (𝓝 0) := by
    have h := (Real.summable_pow_div_factorial (Q*J*t)).tendsto_atTop_zero.const_mul (M*exp (c*|x|))
    convert h using 1
    · funext n
      rw [mul_pow]
      ring
    · simp
  have hz : |u t x| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall (fun n => hbound n t ht x))
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

/-- Every continuous mild solution with a uniform exponential spatial bound
agrees on the strip with the constructed potential-heat field. -/
theorem eq_potentialHeatSolution_of_mild {q u : ℝ → ℝ → ℝ} {g : ℝ → ℝ} {ν T Q : ℝ}
    (hν : 0 ≤ ν) (hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hQ : 0 ≤ Q) (hqb : ∀ t ∈ Icc 0 T, ∀ x, |q t x| ≤ Q)
    (hg : Continuous g) (hgg : HasExpGrowth g)
    (hu : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hug : HeatWholeLine.HasExpGrowthOnStrip u T)
    (he : ∀ t ∈ Icc 0 T, ∀ x, u t x = heatSolution g (ν * t) x +
      heatDuhamel ν (fun s y => q s y * u s y) t x)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : ℝ) : u t x = potentialHeatSolution ν q g t x := by
  have hv := potentialHeatSolution_continuousOn hν (ht.1.trans ht.2) hq hQ hqb hg hgg
  have hvg := potentialHeatSolution_hasExpGrowthOnStrip hν hq hQ hqb hg hgg
  have hneg : HeatWholeLine.HasExpGrowthOnStrip
      (fun s y => -q s y * potentialHeatSolution ν q g s y) T := by
    apply mul_strip_growth hvg hQ
    intro s hs y
    simpa only [abs_neg] using hqb s hs y
  have hd : ∀ s ∈ Icc 0 T, ∀ y,
      u s y - potentialHeatSolution ν q g s y =
        heatDuhamel ν (fun r z => q r z * (u r z - potentialHeatSolution ν q g r z)) s y := by
    intro s hs y
    have hsum := heatDuhamel_add (f := fun r z => q r z * u r z)
      (g := fun r z => -q r z * potentialHeatSolution ν q g r z)
      (hq.mul hu) (hq.neg.mul hv) (mul_strip_growth hug hQ hqb) hneg ν hs y
    have hfun : (fun r z => q r z * u r z + -q r z * potentialHeatSolution ν q g r z) =
        fun r z => q r z * (u r z - potentialHeatSolution ν q g r z) := by
      funext r z; ring
    have hfunneg : (fun r z => -q r z * potentialHeatSolution ν q g r z) =
        fun r z => (-1) * (q r z * potentialHeatSolution ν q g r z) := by
      funext r z; ring
    rw [hfun,hfunneg,heatDuhamel_const_mul] at hsum
    rw [hsum,he s hs y,potentialHeatSolution_mild hν hq hQ hqb hg hgg hs y]
    ring
  exact sub_eq_zero.mp (eq_zero_of_homogeneous_mild
    (u := fun s y => u s y - potentialHeatSolution ν q g s y) hν hq hQ hqb
    (hu.sub hv) (hug.sub hvg) hd ht x)

end MathlibExt.Analysis.PDE.HeatKernel
