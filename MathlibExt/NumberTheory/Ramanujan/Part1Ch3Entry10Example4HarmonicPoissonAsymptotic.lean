/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.SpecialFunctions.Gamma.RegularizedIntegral
import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Entry10Example4Summable

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

private noncomputable def Harm (k : ℕ) : ℝ := ((harmonic k : ℚ) : ℝ)

/-- `Harm` agrees with the explicit harmonic sum in the main theorem. -/
private lemma Harm_eq_sum (k : ℕ) :
    Harm k = ∑ j ∈ Finset.Icc 1 k, (1 : ℝ) / (j : ℝ) := by
  have h := _root_.harmonic_eq_sum_Icc (n := k)
  have h2 : ((∑ i ∈ Finset.Icc 1 k, (↑i)⁻¹ : ℚ) : ℝ) = (((_root_.harmonic k : ℚ)) : ℝ) := by
    rw [← h]
  unfold Harm
  rw [← h2]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [one_div]

private lemma Harm_zero : Harm 0 = 0 := by
  simp [Harm, harmonic]

private lemma Harm_nonneg (k : ℕ) : 0 ≤ Harm k := by
  rw [Harm_eq_sum]
  apply Finset.sum_nonneg
  intro j _
  positivity

private lemma Harm_le (k : ℕ) : Harm k ≤ (k : ℝ) := by
  rw [Harm_eq_sum]
  calc (∑ j ∈ Finset.Icc 1 k, (1 : ℝ) / (j : ℝ))
      ≤ ∑ _j ∈ Finset.Icc 1 k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
          have h1j : 1 ≤ j := (Finset.mem_Icc.mp hj).1
          exact_mod_cast h1j
        rw [div_le_one (by positivity)]
        exact hj1
    _ = (k : ℝ) := by
        simp [Finset.sum_const, Nat.card_Icc]

private lemma Harm_succ (m : ℕ) : Harm (m + 1) - Harm m = 1 / ((m : ℝ) + 1) := by
  rw [Harm_eq_sum, Harm_eq_sum]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  rw [add_sub_cancel_left]
  norm_cast

private lemma summable_Harm_term (x : ℝ) :
    Summable (fun k : ℕ => x ^ k * Harm k / (k.factorial : ℝ)) := by
  have h :=
    Entry10Example4Summable.ramanujan_part1_ch3_entry10_example4_summable x
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have key : ∀ (k : ℕ) (a f : ℝ),
      Real.exp x * (Real.exp (-x) * x ^ k * a / f) = x ^ k * a / f := by
    intro k a f
    calc Real.exp x * (Real.exp (-x) * x ^ k * a / f)
        = (Real.exp x * Real.exp (-x)) * (x ^ k * a / f) := by ring
      _ = x ^ k * a / f := by rw [hexp, one_mul]
  have h2 := h.mul_left (Real.exp x)
  refine h2.congr (fun k => ?_)
  rw [Harm_eq_sum]
  exact key k _ _

/-- The continuous extension of `(1 - e^{-u}) / u` to `u = 0` (value `1` there). -/
private noncomputable def hdiv (u : ℝ) : ℝ := if u = 0 then 1 else (1 - Real.exp (-u)) / u

private lemma hasDerivAt_exp_neg_zero :
    HasDerivAt (fun u : ℝ => Real.exp (-u)) (-1) 0 := by
  have h1 := (hasDerivAt_id (0 : ℝ)).neg
  have h2 : HasDerivAt Real.exp (Real.exp (-(0 : ℝ))) (-(0 : ℝ)) :=
    Real.hasDerivAt_exp _
  have h3 := h2.comp 0 h1
  simpa [Function.comp_def, id_eq] using h3

private lemma tendsto_g_punctured :
    Filter.Tendsto (fun u : ℝ => (1 - Real.exp (-u)) / u)
      (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  have hlim := hasDerivAt_exp_neg_zero.tendsto_slope
  have hneg := hlim.neg
  rw [neg_neg] at hneg
  refine hneg.congr fun u => ?_
  simp only [slope, smul_eq_mul, vsub_eq_sub, sub_zero]
  have h0 : Real.exp (-(0 : ℝ)) = 1 := by simp
  rw [h0]
  ring

private lemma continuousAt_g {u : ℝ} (hu : u ≠ 0) :
    ContinuousAt (fun u : ℝ => (1 - Real.exp (-u)) / u) u := by
  have hexp : ContinuousAt (fun u : ℝ => Real.exp (-u)) u :=
    (Real.continuous_exp.comp continuous_neg).continuousAt
  exact (continuousAt_const.sub hexp).div continuousAt_id hu

private lemma hdiv_continuous : Continuous hdiv := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    have heq : hdiv = Function.update (fun u : ℝ => (1 - Real.exp (-u)) / u) 0 1 := by
      funext v
      by_cases hv : v = 0
      · simp [hdiv, hv, Function.update_self]
      · simp [hdiv, hv, Function.update_of_ne]
    rw [heq, continuousAt_update_same]
    exact tendsto_g_punctured
  · refine ContinuousAt.congr (continuousAt_g hu) ?_
    filter_upwards [compl_singleton_mem_nhds hu] with v hv
    have hv0 : v ≠ 0 := hv
    simp only [hdiv, hv0, ite_false]

private noncomputable def S (x : ℝ) : ℝ := ∑' k : ℕ, x ^ k * (Harm k / (k.factorial : ℝ))

private noncomputable def E (x : ℝ) : ℝ := Real.exp (-x) * S x

private lemma S_eq_tsum (x : ℝ) :
    S x = ∑' k : ℕ, x ^ k * Harm k / (k.factorial : ℝ) := by
  unfold S
  apply tsum_congr
  intro k
  ring

private lemma S_zero : S 0 = 0 := by
  have h0 : ∀ k : ℕ, (0 : ℝ) ^ k * (Harm k / (k.factorial : ℝ)) = 0 := by
    intro k
    cases k with
    | zero => simp [Harm_zero]
    | succ k => simp
  unfold S
  simp [h0]

private lemma E_zero : E 0 = 0 := by
  simp [E, S_zero]

private lemma S'bound_summable (B : ℝ) (hB : 1 ≤ B) :
    Summable (fun n : ℕ => (n : ℝ) * (n : ℝ) * B ^ n / (n.factorial : ℝ)) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hbase := Real.summable_pow_div_factorial (4 * B)
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) * (n : ℝ) * B ^ n / (n.factorial : ℝ) := by
    intro n
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply mul_nonneg _ (pow_nonneg hB0 n)
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine Summable.of_nonneg_of_le (fun n => hnn n) ?_ hbase
  intro n
  have hn2 : (n : ℝ) ≤ (2 ^ n : ℝ) := by
    have h : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
    have h2 : ((n : ℕ) : ℝ) ≤ (((2 ^ n : ℕ)) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_pow, Nat.cast_two] at h2
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have h4 : (n : ℝ) * (n : ℝ) ≤ (4 ^ n : ℝ) := by
    calc (n : ℝ) * (n : ℝ) ≤ (2 ^ n : ℝ) * (2 ^ n : ℝ) :=
          mul_le_mul hn2 hn2 (by positivity) (by positivity)
      _ = (4 ^ n : ℝ) := by rw [← mul_pow]; norm_num
  have hBle : (0 : ℝ) ≤ B ^ n := pow_nonneg hB0 n
  calc (n : ℝ) * (n : ℝ) * B ^ n / (n.factorial : ℝ)
      ≤ (4 ^ n : ℝ) * B ^ n / (n.factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hfact)
        exact mul_le_mul_of_nonneg_right h4 hBle
    _ = (4 * B) ^ n / (n.factorial : ℝ) := by rw [mul_pow]

private lemma S'term_norm_le (B : ℝ) (hB : 1 ≤ B) (y : ℝ) (hyB : ‖y‖ ≤ B) (n : ℕ) :
    ‖(↑n * y ^ (n - 1)) * (Harm n / (n.factorial : ℝ))‖
      ≤ (n : ℝ) * (n : ℝ) * B ^ n / (n.factorial : ℝ) := by
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hHnn : 0 ≤ Harm n / (n.factorial : ℝ) :=
    div_nonneg (Harm_nonneg n) (le_of_lt hfact)
  have hyn : 0 ≤ ‖y‖ := norm_nonneg _
  have hnnorm : ‖((n : ℕ) : ℝ)‖ = (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  have hHnorm : ‖Harm n / (n.factorial : ℝ)‖ = Harm n / (n.factorial : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hHnn]
  have h1 : ‖y‖ ^ (n - 1) ≤ B ^ (n - 1) := pow_le_pow_left₀ hyn hyB (n - 1)
  have h2 : B ^ (n - 1) ≤ B ^ n := pow_le_pow_right₀ hB (Nat.sub_le n 1)
  have h3 : Harm n / (n.factorial : ℝ) ≤ (n : ℝ) / (n.factorial : ℝ) :=
    div_le_div_of_nonneg_right (Harm_le n) (le_of_lt hfact)
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [norm_mul, norm_mul, norm_pow, hnnorm, hHnorm]
  calc (n : ℝ) * ‖y‖ ^ (n - 1) * (Harm n / (n.factorial : ℝ))
      ≤ (n : ℝ) * B ^ n * ((n : ℝ) / (n.factorial : ℝ)) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ hnR
          exact le_trans h1 h2
        · exact h3
        · exact hHnn
        · exact mul_nonneg hnR (pow_nonneg hB0 n)
    _ = (n : ℝ) * (n : ℝ) * B ^ n / (n.factorial : ℝ) := by ring

private lemma summable_S'_term (x : ℝ) :
    Summable (fun n : ℕ => (↑n * x ^ (n - 1)) * (Harm n / (n.factorial : ℝ))) := by
  have hB : (1 : ℝ) ≤ ‖x‖ + 1 := by
    have h := norm_nonneg x
    linarith
  have hxB : ‖x‖ ≤ ‖x‖ + 1 := by linarith [norm_nonneg x]
  refine Summable.of_norm_bounded (S'bound_summable (‖x‖ + 1) hB) fun n => ?_
  exact S'term_norm_le _ hB _ hxB n

/-- Termwise derivative of the Poisson-harmonic power series on a ball. -/
private lemma hasDerivAt_S (x₀ : ℝ) :
    HasDerivAt S (∑' n : ℕ, (↑n * x₀ ^ (n - 1)) * (Harm n / (n.factorial : ℝ))) x₀ := by
  have hB : (1 : ℝ) ≤ ‖x₀‖ + 1 := by
    have h := norm_nonneg x₀
    linarith
  have hBu : Summable (fun n : ℕ => (n : ℝ) * (n : ℝ) * (‖x₀‖ + 1) ^ n / (n.factorial : ℝ)) :=
    S'bound_summable _ hB
  have hmem : ∀ y : ℝ, y ∈ Metric.ball x₀ 1 → ‖y‖ ≤ ‖x₀‖ + 1 := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    calc ‖y‖ = ‖x₀ + (y - x₀)‖ := by ring_nf
      _ ≤ ‖x₀‖ + ‖y - x₀‖ := norm_add_le _ _
      _ ≤ ‖x₀‖ + 1 := by linarith [hy]
  have hder : ∀ n y, y ∈ Metric.ball x₀ 1 →
      HasDerivAt (fun y : ℝ => y ^ n * (Harm n / (n.factorial : ℝ)))
      ((↑n * y ^ (n - 1)) * (Harm n / (n.factorial : ℝ))) y := by
    intro n y _
    exact (hasDerivAt_pow n y).mul_const _
  have hbnd : ∀ n y, y ∈ Metric.ball x₀ 1 →
      ‖(↑n * y ^ (n - 1)) * (Harm n / (n.factorial : ℝ))‖
        ≤ (n : ℝ) * (n : ℝ) * (‖x₀‖ + 1) ^ n / (n.factorial : ℝ) := by
    intro n y hy
    exact S'term_norm_le _ hB _ (hmem y hy) n
  have hg0 : Summable (fun n : ℕ => x₀ ^ n * (Harm n / (n.factorial : ℝ))) := by
    simpa [mul_div_assoc] using summable_Harm_term x₀
  have hxmem : x₀ ∈ Metric.ball x₀ 1 := Metric.mem_ball_self (by norm_num)
  have hmain := hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => (n : ℝ) * (n : ℝ) * (‖x₀‖ + 1) ^ n / (n.factorial : ℝ))
    hBu Metric.isOpen_ball Metric.isPreconnected_ball hder hbnd hxmem hg0 hxmem
  exact hmain

private lemma exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  apply tsum_congr
  intro n
  simp [div_eq_mul_inv, smul_eq_mul, mul_comm]

private lemma S'shift_term (x : ℝ) (m : ℕ) :
    (↑(m + 1) * x ^ (m + 1 - 1)) * (Harm (m + 1) / ((((m + 1 : ℕ)).factorial : ℕ) : ℝ))
      = Harm (m + 1) * x ^ m / (m.factorial : ℝ) := by
  have hfact : ((m.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have e1 : ((((m + 1 : ℕ)).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e2 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have e3 : m + 1 - 1 = m := Nat.add_sub_cancel m 1
  rw [e3, e1, e2]
  field_simp

private lemma S'_shift (x : ℝ) :
    (∑' n : ℕ, (↑n * x ^ (n - 1)) * (Harm n / (n.factorial : ℝ)))
      = ∑' m : ℕ, Harm (m + 1) * x ^ m / (m.factorial : ℝ) := by
  have hS := summable_S'_term x
  have h1 := hS.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1
  have hd0 : (↑(0 : ℕ) * x ^ (0 - 1)) * (Harm 0 / ((((0 : ℕ)).factorial : ℕ) : ℝ)) = 0 := by
    simp [Harm_zero]
  rw [hd0, zero_add] at h1
  rw [← h1]
  apply tsum_congr
  intro m
  exact S'shift_term x m

private lemma S'shift_summable (x : ℝ) :
    Summable (fun m : ℕ => Harm (m + 1) * x ^ m / (m.factorial : ℝ)) := by
  have heq : (fun m : ℕ => Harm (m + 1) * x ^ m / (m.factorial : ℝ))
      = (fun m : ℕ => (↑(m + 1) * x ^ (m + 1 - 1)) *
          (Harm (m + 1) / ((((m + 1 : ℕ)).factorial : ℕ) : ℝ))) := by
    funext m
    exact (S'shift_term x m).symm
  rw [heq]
  exact (summable_nat_add_iff 1).mpr (summable_S'_term x)

private lemma hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  have hneg := (hasDerivAt_id x).neg
  have hexp := (Real.hasDerivAt_exp _).comp x hneg
  simpa [Function.comp_def, id_eq] using hexp

private lemma hasDerivAt_E (x : ℝ) :
    HasDerivAt E (Real.exp (-x) *
      ((∑' m : ℕ, Harm (m + 1) * x ^ m / (m.factorial : ℝ)) - S x)) x := by
  have hS := hasDerivAt_S x
  rw [S'_shift x] at hS
  have hmul := (hasDerivAt_exp_neg x).mul hS
  refine hmul.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · apply Filter.Eventually.of_forall
    intro y
    rfl
  · ring

private lemma geom_tail (x : ℝ) (hx : x ≠ 0) :
    (∑' m : ℕ, x ^ m / ((((m + 1 : ℕ)).factorial) : ℝ)) = (Real.exp x - 1) / x := by
  have hbase : Summable (fun m : ℕ => x ^ m / (m.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  have h1 := hbase.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at h1
  have hf0 : x ^ 0 / (((((0 : ℕ)).factorial : ℕ)) : ℝ) = 1 := by simp
  rw [hf0, ← exp_eq_tsum x] at h1
  have hstep : (∑' m : ℕ, x * (x ^ m / ((((m + 1 : ℕ)).factorial) : ℝ)))
      = ∑' m : ℕ, x ^ (m + 1) / ((((m + 1 : ℕ)).factorial) : ℝ) := by
    apply tsum_congr
    intro m
    rw [pow_succ]
    ring
  have hT : (∑' m : ℕ, x * (x ^ m / ((((m + 1 : ℕ)).factorial) : ℝ))) = Real.exp x - 1 := by
    rw [hstep]
    linarith [h1]
  have hxG : x * (∑' m : ℕ, x ^ m / ((((m + 1 : ℕ)).factorial) : ℝ)) = Real.exp x - 1 := by
    rw [← tsum_mul_left]
    exact hT
  rw [eq_div_iff_mul_eq hx, mul_comm]
  exact hxG

private lemma closed_form (x : ℝ) (hx : x ≠ 0) :
    (∑' m : ℕ, Harm (m + 1) * x ^ m / (m.factorial : ℝ)) - S x
      = (Real.exp x - 1) / x := by
  have hshift := S'shift_summable x
  have hSsum : Summable (fun m : ℕ => x ^ m * (Harm m / (m.factorial : ℝ))) := by
    simpa [mul_div_assoc] using summable_Harm_term x
  have hSS : S x = ∑' m : ℕ, x ^ m * (Harm m / (m.factorial : ℝ)) := rfl
  have hsub : (∑' m : ℕ, (Harm (m + 1) - Harm m) * x ^ m / (m.factorial : ℝ))
      = (∑' m : ℕ, Harm (m + 1) * x ^ m / (m.factorial : ℝ)) - S x := by
    rw [hSS, ← Summable.tsum_sub hshift hSsum]
    apply tsum_congr
    intro m
    ring
  rw [← hsub]
  have heq : (∑' m : ℕ, (Harm (m + 1) - Harm m) * x ^ m / (m.factorial : ℝ))
      = (∑' m : ℕ, x ^ m / ((((m + 1 : ℕ)).factorial) : ℝ)) :=
    tsum_congr fun m => by
      rw [Harm_succ m]
      have e1 : ((((m + 1 : ℕ)).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [e1]
      have hfact : ((m.factorial : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
  rw [heq]
  exact geom_tail x hx

private lemma hasDerivAt_E_hdiv (x : ℝ) : HasDerivAt E (hdiv x) x := by
  have hE := hasDerivAt_E x
  have hval : Real.exp (-x) *
      ((∑' m : ℕ, Harm (m + 1) * x ^ m / (m.factorial : ℝ)) - S x) = hdiv x := by
    by_cases hx : x = 0
    · subst hx
      have hvan : ∀ m' : ℕ, m' ≠ 0 →
          Harm (m' + 1) * (0 : ℝ) ^ m' / ((m'.factorial : ℕ) : ℝ) = 0 := by
        intro m hm
        cases m with
        | zero => exact absurd rfl hm
        | succ k => simp [pow_succ]
      have hSh : (∑' m : ℕ, Harm (m + 1) * (0 : ℝ) ^ m / (m.factorial : ℝ)) = 1 := by
        have hts : (∑' m : ℕ, Harm (m + 1) * (0 : ℝ) ^ m / ((m.factorial : ℕ) : ℝ))
            = (fun m : ℕ => Harm (m + 1) * (0 : ℝ) ^ m / ((m.factorial : ℕ) : ℝ)) 0 :=
          tsum_eq_single 0 hvan
        rw [hts]
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
        have h1 := Harm_succ 0
        rw [Harm_zero] at h1
        simpa using h1
      rw [S_zero, hSh]
      simp [hdiv]
    · rw [closed_form x hx]
      have hexp : Real.exp (-x) * Real.exp x = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      simp only [hdiv, hx, ite_false]
      have hfactor : Real.exp (-x) * ((Real.exp x - 1) / x)
          = (Real.exp (-x) * Real.exp x - Real.exp (-x)) / x := by ring
      rw [hfactor, hexp]
  exact hE.congr_deriv hval

private noncomputable def G (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, hdiv t

private lemma hasDerivAt_G (x : ℝ) : HasDerivAt G (hdiv x) x := by
  unfold G
  exact intervalIntegral.integral_hasDerivAt_right (hdiv_continuous.intervalIntegrable 0 x)
    (hdiv_continuous.stronglyMeasurable.stronglyMeasurableAtFilter) hdiv_continuous.continuousAt

private lemma G_zero : G 0 = 0 := by
  unfold G
  simp

private lemma E_eq_G : E = G := by
  have hfE : Differentiable ℝ E := fun x => (hasDerivAt_E_hdiv x).differentiableAt
  have hfG : Differentiable ℝ G := fun x => (hasDerivAt_G x).differentiableAt
  have hfeq : ∀ x, fderiv ℝ E x = fderiv ℝ G x := by
    intro x
    rw [(hasDerivAt_E_hdiv x).hasFDerivAt.fderiv, (hasDerivAt_G x).hasFDerivAt.fderiv]
  have h0 : E 0 = G 0 := by
    rw [E_zero, G_zero]
  exact eq_of_fderiv_eq hfE hfG hfeq 0 h0

private lemma integral_one_div_log (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ s in a..b, 1 / s) = Real.log (b / a) := by
  simp only [one_div]
  exact integral_inv_of_pos ha hb

private lemma integrable_G :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s) / s) (Set.Ioi 1) := by
  have hexp : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-s)) (Set.Ioi 1) := by
    have h := exp_neg_integrableOn_Ioi (1:ℝ) (show (0:ℝ) < 1 by norm_num)
    simpa using h
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.exp (-s) / s)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.div
    · exact Real.measurable_exp.comp measurable_neg
    · exact measurable_id
  refine MeasureTheory.Integrable.mono' hexp hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : (1:ℝ) ≤ s := le_of_lt (Set.mem_Ioi.mp hs)
  have hs0 : (0:ℝ) ≤ s := by linarith
  have e1 : (0:ℝ) ≤ Real.exp (-s) := (Real.exp_pos _).le
  have e2 : (0:ℝ) ≤ Real.exp (-s) / s := div_nonneg e1 hs0
  rw [Real.norm_eq_abs, abs_of_nonneg e2]
  exact div_le_self e1 hs1

private noncomputable def C0 : ℝ := ∫ t in (0:ℝ)..1, hdiv t

private noncomputable def Finf (s : ℝ) : ℝ := Real.exp (-s) / s

private noncomputable def L : ℝ :=
  ∫ s in Set.Ioi (1:ℝ), Finf s ∂MeasureTheory.volume

private lemma gamma_eq : Real.eulerMascheroniConstant = C0 - L := by
  have hC0 : ((C0 : ℝ) : ℂ)
      = ∫ t : ℝ in (0:ℝ)..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ) := by
    have hcongr : (∫ t : ℝ in (0:ℝ)..1, ((hdiv t : ℝ) : ℂ))
        = ∫ t : ℝ in (0:ℝ)..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_uIoo (μ := MeasureTheory.volume)
      intro x hx
      rw [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioo] at hx
      have hx0 : x ≠ 0 := ne_of_gt hx.1
      simp only [hdiv, hx0, ite_false]
    unfold C0
    rw [← intervalIntegral.integral_ofReal]
    exact hcongr
  have hL : ((L : ℝ) : ℂ)
      = ∫ t : ℝ in Set.Ioi (1:ℝ), ((Real.exp (-t) / t : ℝ) : ℂ) := by
    unfold L Finf
    rw [← integral_complex_ofReal]
  have h := Real.eulerMascheroniConstant_eq_regularized_integrals
  apply Complex.ofReal_injective
  push_cast
  rw [hC0, hL]
  exact h

private lemma integral_exp_neg (a b : ℝ) :
    (∫ s in a..b, Real.exp (-s)) = Real.exp (-a) - Real.exp (-b) := by
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => -Real.exp (-s)) (Real.exp (-s)) s := by
    intro s _
    exact ((hasDerivAt_exp_neg s).neg).congr_deriv (neg_neg _)
  have hcont : Continuous (fun s : ℝ => Real.exp (-s)) :=
    Real.continuous_exp.comp continuous_neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable a b)
  have hring : (-Real.exp (-b)) - (-Real.exp (-a)) = Real.exp (-a) - Real.exp (-b) := by
    ring
  rwa [hring] at hftc

private lemma Finf_integrable (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable Finf MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hmem : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  unfold Finf
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  · exact continuousOn_id
  · intro s hs
    rw [hmem] at hs
    have h1s : a ≤ s := hs.1
    linarith

private lemma tendsto_L :
    Filter.Tendsto (fun n : ℕ => ∫ s in (1:ℝ)..(n:ℝ), Finf s) Filter.atTop (nhds L) := by
  have hmono : Monotone (fun n : ℕ => Set.Ioc (1:ℝ) (n:ℝ)) := by
    intro m n hmn
    apply Set.Ioc_subset_Ioc_right
    exact_mod_cast hmn
  have hunion : (⋃ n : ℕ, Set.Ioc (1:ℝ) (n:ℝ)) = Set.Ioi 1 := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨n, h1s, _⟩
      exact h1s
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_gt s
      exact ⟨n, hs, le_of_lt hn⟩
  have hfi : MeasureTheory.IntegrableOn Finf (⋃ n : ℕ, Set.Ioc (1:ℝ) (n:ℝ)) := by
    rw [hunion]
    exact integrable_G
  have hlim := MeasureTheory.tendsto_setIntegral_of_monotone
    (fun n : ℕ => measurableSet_Ioc) hmono hfi
  rw [hunion] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (intervalIntegral.integral_of_le (by exact_mod_cast hn)).symm

private lemma E_sub_log_gamma (x : ℝ) (hx : 1 ≤ x) :
    E x - (Real.log x + Real.eulerMascheroniConstant)
      = L - (∫ s in (1:ℝ)..x, Finf s) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hEG : E x = G x := congrFun E_eq_G x
  have hG : G x = C0 + (∫ s in (1:ℝ)..x, hdiv s) := by
    unfold G C0
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hdiv_continuous.intervalIntegrable 0 1)
      (hdiv_continuous.intervalIntegrable 1 x)).symm
  have hmem : Set.uIcc (1:ℝ) x = Set.Icc 1 x := Set.uIcc_of_le hx
  have hne : ∀ s ∈ Set.uIcc (1:ℝ) x, s ≠ 0 := by
    intro s hs
    rw [hmem] at hs
    linarith [hs.1]
  have hhdiv : (∫ s in (1:ℝ)..x, hdiv s)
      = (∫ s in (1:ℝ)..x, 1/s) - (∫ s in (1:ℝ)..x, Finf s) := by
    have hpt : ∀ s ∈ Set.uIcc (1:ℝ) x, hdiv s = 1/s - Finf s := by
      intro s hs
      have hs0 := hne s hs
      unfold Finf
      simp only [hdiv, hs0, ite_false]
      ring
    have heq : (∫ s in (1:ℝ)..x, hdiv s) = ∫ s in (1:ℝ)..x, (1/s - Finf s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hpt s hs
    rw [heq]
    apply intervalIntegral.integral_sub
    · have hc : ContinuousOn (fun s : ℝ => (1:ℝ)/s) (Set.uIcc 1 x) := by
        simp only [one_div]
        exact continuousOn_id.inv₀ (fun x hx => hne x hx)
      exact hc.intervalIntegrable
    · have hc : ContinuousOn Finf (Set.uIcc 1 x) := by
        unfold Finf
        apply ContinuousOn.div
        · exact (Real.continuous_exp.comp continuous_neg).continuousOn
        · exact continuousOn_id
        · intro s hs
          exact hne s hs
      exact hc.intervalIntegrable
  have hlog : (∫ s in (1:ℝ)..x, 1/s) = Real.log x := by
    have h := integral_one_div_log 1 x (by norm_num) hx0
    rwa [div_one] at h
  have hCg : C0 - Real.eulerMascheroniConstant = L := by
    have h := gamma_eq
    linarith
  rw [hEG, hG, hhdiv, hlog]
  linear_combination hCg

private lemma eventually_ge_cast (x : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, x ≤ ((n : ℕ) : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop x)

private lemma tendsto_diff_lim (x : ℝ) (hx : 1 ≤ x) :
    Filter.Tendsto (fun n : ℕ => ∫ s in x..(n:ℝ), Finf s) Filter.atTop
      (nhds (L - (∫ s in (1:ℝ)..x, Finf s))) := by
  have hc : Filter.Tendsto (fun _ : ℕ => ∫ s in (1:ℝ)..x, Finf s) Filter.atTop
      (nhds (∫ s in (1:ℝ)..x, Finf s)) :=
    tendsto_const_nhds
  have hL := tendsto_L.sub hc
  apply hL.congr'
  filter_upwards [eventually_ge_cast x] with n hn
  have hsplit : (∫ s in (1:ℝ)..(n:ℝ), Finf s)
      = (∫ s in (1:ℝ)..x, Finf s) + (∫ s in x..(n:ℝ), Finf s) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (Finf_integrable 1 x (by norm_num) hx)
      (Finf_integrable x (n:ℝ) (by linarith) hn)).symm
  linarith [hsplit]

private lemma interval_nonneg (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : x ≤ (n : ℝ)) :
    0 ≤ ∫ s in x..(n:ℝ), Finf s := by
  apply intervalIntegral.integral_nonneg (by exact_mod_cast hn)
  intro s hs
  have hsx : x ≤ s := hs.1
  have hs0 : (0:ℝ) < s := by linarith
  unfold Finf
  exact div_nonneg (Real.exp_pos _).le hs0.le

private lemma interval_le (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : x ≤ (n : ℝ)) :
    (∫ s in x..(n:ℝ), Finf s) ≤ 1 / x := by
  have hx0 : (0:ℝ) < x := by linarith
  have hle : (∫ s in x..(n:ℝ), Finf s) ≤ (∫ s in x..(n:ℝ), Real.exp (-s)/x) := by
    apply intervalIntegral.integral_mono_on (by exact_mod_cast hn)
    · exact Finf_integrable x (n:ℝ) hx0 (by exact_mod_cast hn)
    · have hc : Continuous (fun s : ℝ => Real.exp (-s)/x) := by fun_prop
      exact hc.intervalIntegrable x (n:ℝ)
    · intro s hs
      have hsx : x ≤ s := hs.1
      have hs0 : (0:ℝ) < s := by linarith
      have h1 : (1:ℝ)/s ≤ 1/x := one_div_le_one_div_of_le hx0 hsx
      have h2 : Real.exp (-s) * (1/s) ≤ Real.exp (-s) * (1/x) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      have e1 : Real.exp (-s)/s = Real.exp (-s)*(1/s) := div_eq_mul_one_div _ _
      have e2 : Real.exp (-s)/x = Real.exp (-s)*(1/x) := div_eq_mul_one_div _ _
      unfold Finf
      rw [e1, e2]
      exact h2
  have heq : (∫ s in x..(n:ℝ), Real.exp (-s)/x)
      = (Real.exp (-x) - Real.exp (-(n:ℝ)))/x := by
    rw [intervalIntegral.integral_div, integral_exp_neg]
  have hfin : (Real.exp (-x) - Real.exp (-(n:ℝ)))/x ≤ 1/x := by
    apply div_le_div_of_nonneg_right _ hx0.le
    have e1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have e2 : (0:ℝ) ≤ Real.exp (-(n:ℝ)) := (Real.exp_pos _).le
    linarith
  calc (∫ s in x..(n:ℝ), Finf s) ≤ (∫ s in x..(n:ℝ), Real.exp (-s)/x) := hle
    _ = (Real.exp (-x) - Real.exp (-(n:ℝ)))/x := heq
    _ ≤ 1/x := hfin

private lemma diff_nonneg (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ E x - (Real.log x + Real.eulerMascheroniConstant) := by
  rw [E_sub_log_gamma x hx]
  apply ge_of_tendsto (tendsto_diff_lim x hx)
  filter_upwards [eventually_ge_cast x] with n hn
  exact interval_nonneg x hx n hn

private lemma diff_le (x : ℝ) (hx : 1 ≤ x) :
    E x - (Real.log x + Real.eulerMascheroniConstant) ≤ 1 / x := by
  rw [E_sub_log_gamma x hx]
  apply le_of_tendsto (tendsto_diff_lim x hx)
  filter_upwards [eventually_ge_cast x] with n hn
  exact interval_le x hx n hn

private lemma E_eq_thm (x : ℝ) : E x = Real.exp (-x) *
    (∑' k : ℕ, x ^ k * Harm k / (k.factorial : ℝ)) := by
  unfold E
  rw [S_eq_tsum]

/-- **Asymptotics of the harmonic Poisson series.** Let $H_k = \sum_{j=1}^{k} 1/j$ be the $k$-th
harmonic number (so $H_0 = 0$) and let $\gamma$ be the Euler–Mascheroni constant. Then, as
$x \to \infty$,
$$e^{-x} \sum_{k=0}^{\infty} \frac{x^k H_k}{k!} = \log x + \gamma + O\left(\frac{1}{x}\right).$$

Proves `Wanted` entry `ramanujan_part1_ch3_entry10_example4_harmonic_poisson_asymptotic`.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, Example 4, printed pp.
    65-66 / PDF pp. 75-76.
-/
theorem ramanujan_part1_ch3_entry10_example4_harmonic_poisson_asymptotic :
    Asymptotics.IsBigO Filter.atTop (fun x : ℝ => Real.exp (-x) *
        (∑' (k : ℕ),
            (x ^ k * (∑ j ∈ Finset.Icc 1 k, (1 : ℝ) / (j : ℝ)) /
                (k.factorial : ℝ))) - (Real.log x + Real.eulerMascheroniConstant)) (fun x : ℝ =>
                (1 : ℝ) / x) := by
  have hF : (fun x : ℝ => Real.exp (-x) *
      (∑' (k : ℕ), (x ^ k * (∑ j ∈ Finset.Icc 1 k, (1 : ℝ) / (j : ℝ)) / (k.factorial : ℝ))) -
        (Real.log x + Real.eulerMascheroniConstant))
      = (fun x => E x - (Real.log x + Real.eulerMascheroniConstant)) := by
    funext x
    have h1 : (∑' k : ℕ, x ^ k * (∑ j ∈ Finset.Icc 1 k, (1:ℝ)/(j:ℝ)) / (k.factorial:ℝ))
        = ∑' k : ℕ, x ^ k * Harm k / (k.factorial:ℝ) :=
      tsum_congr fun k => by rw [Harm_eq_sum]
    rw [h1, ← E_eq_thm]
  rw [hF]
  apply Filter.Eventually.isBigO
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  show ‖E x - (Real.log x + Real.eulerMascheroniConstant)‖ ≤ 1 / x
  have h0 := diff_nonneg x hx
  have h1 := diff_le x hx
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

end Entry10Example4HarmonicPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
