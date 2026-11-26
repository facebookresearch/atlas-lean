/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.Chemistry.Kinetics.RateLaws

/-!
# Bolus response of equal compartments in series

The finite linear model has a common transfer rate and an initial passive tracer in the first
compartment only. We prove the amount profiles and normalize the last compartment's outflow.
The density formula is from Rawlings and Ekerdt, *Chemical Reactor Analysis and Design
Fundamentals*, 2nd ed., §8.2.5, Eq. 8.16.
-/

namespace Chemistry.Transport

open MeasureTheory
open Chemistry.Kinetics (firstOrderSol firstOrderSol_unique hasDerivAt_firstOrderSol)

private lemma hasDerivAt_amount_succ (a m t : ℝ) (j : ℕ) :
    HasDerivAt (fun s : ℝ ↦ m * ((a * s) ^ (j + 1) / ((j + 1).factorial : ℝ)) *
      Real.exp (-(a * s)))
      (a * (m * ((a * t) ^ j / (j.factorial : ℝ)) * Real.exp (-(a * t)) -
        m * ((a * t) ^ (j + 1) / ((j + 1).factorial : ℝ)) * Real.exp (-(a * t)))) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
    simpa only [mul_one] using (hasDerivAt_id' t).const_mul a
  have hpoly := ((hlin.fun_pow (j + 1)).div_const ((j + 1).factorial : ℝ)).const_mul m
  refine (hpoly.mul hlin.fun_neg.exp).congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  field_simp [hj.ne', hf.ne']
  ring

/-- In a chain of `n + 1` equal compartments with total time parameter `τ > 0`, the common
rate is `a = (n + 1) / τ`. Compartment indices start at zero. With initial amount `m₀ > 0` in
compartment zero and no input after initialization, the displayed profiles solve the initial-value
problem. A solution has an ordinary (two-sided) derivative at every `t ≥ 0`, including zero, and
agrees with these profiles at every such time; no agreement at negative times is claimed.
The final outflow divided by `m₀`, extended by zero for `t < 0`, is a nonnegative measurable
density of integral one. -/
public theorem serialTank_bolusResponse (n : ℕ) (τ m₀ : ℝ) (hτ : 0 < τ) (hm₀ : 0 < m₀) :
    let a : ℝ := (n + 1 : ℕ) / τ
    let N : Fin (n + 1) → ℝ → ℝ := fun j t ↦
      m₀ * ((a * t) ^ (j : ℕ) / ((j : ℕ).factorial : ℝ)) * Real.exp (-(a * t))
    let Solves : (Fin (n + 1) → ℝ → ℝ) → Prop := fun u ↦
      u 0 0 = m₀ ∧ (∀ j : Fin n, u j.succ 0 = 0) ∧
      (∀ t, 0 ≤ t → HasDerivAt (u 0) (-a * u 0 t) t) ∧
      (∀ (j : Fin n) t, 0 ≤ t → HasDerivAt (u j.succ)
        (a * (u j.castSucc t - u j.succ t)) t)
    let p : ℝ → ℝ := fun t ↦
      if 0 ≤ t then a ^ (n + 1) / (n.factorial : ℝ) * t ^ n * Real.exp (-(a * t)) else 0
    Solves N ∧
      (∀ u, Solves u → ∀ j t, 0 ≤ t → u j t = N j t) ∧
      (∀ t, p t = if 0 ≤ t then a * N (Fin.last n) t / m₀ else 0) ∧
      (∀ t, 0 ≤ p t) ∧ Measurable p ∧ (∫ t, p t) = 1 := by
  intro a N Solves p
  have ha : 0 < a := div_pos (by positivity) hτ
  have hfirst : N 0 = firstOrderSol m₀ a := by
    funext t
    simp [N, firstOrderSol, neg_mul]
  have hN : Solves N := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hfirst]
      simp [firstOrderSol]
    · intro j
      simp [N]
    · intro t _
      rw [hfirst]
      exact hasDerivAt_firstOrderSol m₀ a t
    · intro j t _
      exact hasDerivAt_amount_succ a m₀ t j.val
  refine ⟨hN, ?_, ?_, ?_⟩
  · intro u hu j
    obtain ⟨hu₀, hu_succ₀, hdu₀, hdu_succ⟩ := hu
    induction j using Fin.induction with
    | zero =>
      intro t ht
      rw [hfirst]
      exact firstOrderSol_unique m₀ a (u 0) hdu₀ hu₀ t ht
    | succ j ih =>
      intro t ht
      have hd (s : ℝ) (hs : 0 ≤ s) :
          HasDerivAt (fun x ↦ u j.succ x - N j.succ x)
            (-a * (u j.succ s - N j.succ s)) s := by
        have h := (hdu_succ j s hs).fun_sub (hN.2.2.2 j s hs)
        rw [ih s hs] at h
        exact h.congr_deriv (by ring)
      have h₀ : u j.succ 0 - N j.succ 0 = 0 := by
        rw [hu_succ₀ j, hN.2.1 j, sub_self]
      have heq := firstOrderSol_unique 0 a (fun x ↦ u j.succ x - N j.succ x) hd h₀ t ht
      simpa [firstOrderSol, sub_eq_zero] using heq
  · intro t
    by_cases ht : 0 ≤ t
    · simp only [p, N, ht, ite_true, Fin.val_last, mul_pow, pow_succ' a]
      have hf : (0 : ℝ) < (n.factorial : ℝ) := by positivity
      field_simp [hm₀.ne', hf.ne']
    · simp [p, ht]
  · have hp : p = ProbabilityTheory.gammaPDFReal ((n : ℝ) + 1) a := by
      funext t
      simp only [p, ProbabilityTheory.gammaPDFReal, Real.Gamma_nat_eq_factorial,
        add_sub_cancel_right, Real.rpow_natCast]
      rw [← Nat.cast_succ, Real.rpow_natCast]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    rw [hp]
    refine ⟨ProbabilityTheory.gammaPDFReal_nonneg hn ha,
      ProbabilityTheory.measurable_gammaPDFReal _ _, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (ProbabilityTheory.gammaPDFReal_nonneg hn ha))
      (ProbabilityTheory.measurable_gammaPDFReal _ _).aestronglyMeasurable]
    change (∫⁻ t, ProbabilityTheory.gammaPDF ((n : ℝ) + 1) a t).toReal = 1
    rw [ProbabilityTheory.lintegral_gammaPDF_eq_one hn ha, ENNReal.toReal_one]

end Chemistry.Transport
