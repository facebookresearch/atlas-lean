/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.StickyKernel

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Availability of a two-state repairable component -/

open Filter Matrix Topology

namespace ProbabilityTheory

@[expose] public section

/-- **Availability of a two-state repairable component.** State `0` is up and state `1` is
 down. The failure rate is `lam ≥ 0` and the repair rate is `μ ≥ 0`; the initial distribution
 is `(p₀, 1 - p₀)` with `0 ≤ p₀ ≤ 1`. Availability `A t` is the up coordinate of that
 distribution propagated by the transition matrix at time `t`. The generator is a rate
 matrix, `A 0 = p₀`, and `A t` lies in `[0, 1]` at nonnegative times. If `lam + μ > 0`,
 then `A t = μ / (lam + μ) + (p₀ - μ / (lam + μ)) * exp (-(lam + μ) * t)` and its limit
 at infinity is `μ / (lam + μ)`. With both rates zero, `A` stays at `p₀`. With no failures
 and an initially up component it stays at one; with a positive failure rate and no
 repairs its limit is zero. -/
theorem two_state_component_availability (lam μ p₀ : ℝ) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ)
    (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    let Q : Matrix (Fin 2) (Fin 2) ℝ := !![-lam, lam; μ, -μ]
    let A : ℝ → ℝ := fun t => (![p₀, 1 - p₀] ᵥ* ctmcTransition Q t) 0
    IsRateMatrix Q ∧ A 0 = p₀ ∧ (∀ t ≥ 0, A t ∈ Set.Icc (0 : ℝ) 1) ∧
    (0 < lam + μ →
      (∀ t, A t = μ / (lam + μ) + (p₀ - μ / (lam + μ)) * Real.exp (-((lam + μ) * t))) ∧
      Tendsto A atTop (𝓝 (μ / (lam + μ)))) ∧
    (lam = 0 → μ = 0 → ∀ t, A t = p₀) ∧
    (lam = 0 → p₀ = 1 → ∀ t, A t = 1) ∧
    (μ = 0 → 0 < lam → Tendsto A atTop (𝓝 0)) := by
  intro Q A
  have hQ : IsRateMatrix Q := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Q]
    · intro i
      fin_cases i <;> simp [Q, Fin.sum_univ_two]
  have hinit : A 0 = p₀ := by
    simp [A]
  have hfreeze (hl : lam = 0) (hm : μ = 0) (t : ℝ) : A t = p₀ := by
    have hQzero : Q = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Q, hl, hm]
    simp [A, hQzero, ctmcTransition]
  let r : ℝ := μ / (lam + μ)
  have hform (hκ : 0 < lam + μ) (t : ℝ) :
      A t = r + (p₀ - r) * Real.exp (-((lam + μ) * t)) := by
    change (![p₀, 1 - p₀] ᵥ* ctmcTransition !![-lam, lam; μ, -μ] t) 0 = _
    rw [ctmcTransition_twoStateRate hκ.ne', vecMul_apply_eq_sum, Fin.sum_univ_two]
    simp [stickyKernel_apply, r, show (1 : Fin 2) ≠ 0 by decide]
    ring
  have hlim (hκ : 0 < lam + μ) : Tendsto A atTop (𝓝 r) := by
    have hE : Tendsto (fun t : ℝ => Real.exp (-((lam + μ) * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hκ))
    have hC : Tendsto (fun _ : ℝ => r) atTop (𝓝 r) := tendsto_const_nhds
    have hD : Tendsto (fun _ : ℝ => p₀ - r) atTop (𝓝 (p₀ - r)) := tendsto_const_nhds
    have h := hC.add (hD.mul hE)
    simp only [mul_zero, add_zero] at h
    exact h.congr (fun t => (hform hκ t).symm)
  refine ⟨hQ, hinit, ?_, fun hκ => ⟨hform hκ, hlim hκ⟩, hfreeze, ?_, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le (add_nonneg hlam hμ) with hκ | hκ
    · rw [hfreeze (by linarith) (by linarith)]
      exact hp₀
    · let e := Real.exp (-((lam + μ) * t))
      have he₀ : 0 ≤ e := (Real.exp_pos _).le
      have he₁ : e ≤ 1 := by
        simpa only [e, Real.exp_zero] using
          (Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hκ.le ht)))
      have hr₀ : 0 ≤ r := div_nonneg hμ hκ.le
      have hr₁ : r ≤ 1 := (div_le_iff₀ hκ).mpr (by linarith)
      have hmix : A t = e * p₀ + (1 - e) * r := by
        rw [hform hκ]
        change r + (p₀ - r) * e = _
        ring
      rw [hmix]
      refine ⟨add_nonneg (mul_nonneg he₀ hp₀.1) (mul_nonneg (sub_nonneg.mpr he₁) hr₀), ?_⟩
      calc
        e * p₀ + (1 - e) * r ≤ e * 1 + (1 - e) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hp₀.2 he₀)
            (mul_le_mul_of_nonneg_left hr₁ (sub_nonneg.mpr he₁))
        _ = 1 := by ring
  · intro hl hp t
    by_cases hm : μ = 0
    · rw [hfreeze hl hm, hp]
    · rw [hform (by simpa [hl] using lt_of_le_of_ne hμ (Ne.symm hm)), hp]
      simp [r, hl, hm]
  · intro hm hl
    have ht := hlim (add_pos_of_pos_of_nonneg hl hμ)
    simpa [r, hm] using ht

end

end ProbabilityTheory
