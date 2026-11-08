/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.SIR
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Tests for the SIR model: a non-vacuity witness (no transmission, exponential removal),
the disease-free equilibrium, and the threshold, conservation and final-size theorems on it. -/

open Real Filter
open scoped Topology

namespace MathlibExtTest.Biology.Epidemiology.SIR

open MathlibExt.Biology.Epidemiology.SIR

/-- **Non-vacuity witness.** With `β = 0`, `γ = 1`, `N = 1`: `S = 1`, `I(t) = e^{-t}`,
`R(t) = 1 - e^{-t}` solves the SIR system. -/
theorem isSolution_decay :
    IsSolution 0 1 1 (fun _ => 1) (fun t => exp (-t)) (fun t => 1 - exp (-t)) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t (1 : ℝ)
  hasDerivAt_infected t _ := by simpa using (hasDerivAt_neg t).exp
  hasDerivAt_removed t _ := by simpa using ((hasDerivAt_neg t).exp).const_sub 1

/-- The same functions solve the system for population size `N = 2`, where `S + I + R = N`
holds. -/
theorem isSolution_decay_two :
    IsSolution 0 1 2 (fun _ => 1) (fun t => exp (-t)) (fun t => 1 - exp (-t)) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t (1 : ℝ)
  hasDerivAt_infected t _ := by simpa using (hasDerivAt_neg t).exp
  hasDerivAt_removed t _ := by simpa using ((hasDerivAt_neg t).exp).const_sub 1

/-- Junk value outside the domain: with `N = 0` Lean's `a / 0 = 0` removes the infection term,
so the decay functions also "solve" the system with `β = 5`. -/
example : IsSolution 5 1 0 (fun _ => 1) (fun t => exp (-t)) (fun t => 1 - exp (-t)) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t (1 : ℝ)
  hasDerivAt_infected t _ := by simpa using (hasDerivAt_neg t).exp
  hasDerivAt_removed t _ := by simpa using ((hasDerivAt_neg t).exp).const_sub 1

/-- The disease-free state is a solution for every `β, γ, N`. -/
example (β γ N S₀ R₀ : ℝ) : IsSolution β γ N (fun _ => S₀) (fun _ => 0) (fun _ => R₀) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t S₀
  hasDerivAt_infected t _ := by simpa using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_removed t _ := by simpa using hasDerivAt_const t R₀

/-- Conservation on the witness: `S + I + R = 2` at `t = 3`. -/
example : (1 : ℝ) + exp (-3) + (1 - exp (-3)) = 1 + exp (-0) + (1 - exp (-0)) :=
  isSolution_decay.total_eq (t := 3) (by norm_num)

/-- Threshold on the witness: without transmission (`R₀ = 0`) the epidemic does not grow. -/
example : ¬ 0 < deriv (fun t : ℝ => exp (-t)) 0 := by
  rw [isSolution_decay.deriv_infected_pos_iff one_pos one_pos (by simp)]
  norm_num

/-- Threshold, general form: with `γ = 1`, `N = 100`, `S(0) = 50`, `I(0) > 0`, growth iff
`β > 2`. -/
example (β : ℝ) (S I R : ℝ → ℝ) (h : IsSolution β 1 100 S I R) (hS : S 0 = 50)
    (hI : 0 < I 0) : 0 < deriv I 0 ↔ 2 < β := by
  rw [h.deriv_infected_pos_iff one_pos (by norm_num) hI, hS]
  constructor <;> intro <;> linarith

/-- Final size on the witness: `S∞ = 1`, `R∞ = 1`, `R(0) = 0`, `R₀ = 0`. -/
example : (1 : ℝ) = 1 * exp (-(0 / 1 * (1 - (1 - exp (-0))) / 1)) := by
  refine isSolution_decay.final_size one_ne_zero tendsto_const_nhds ?_
  have h : Tendsto (fun t : ℝ => exp (-t)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

/-- Classical final-size equation on the `N = 2` witness: `S∞ = 1 = 1 · e^{-0}`. -/
example : (1 : ℝ) = 1 * exp (-(0 / 1 * (2 - 1) / 2)) := by
  refine isSolution_decay_two.final_size_eq one_ne_zero (by norm_num) (by simp)
    tendsto_const_nhds ?_
  exact tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

end MathlibExtTest.Biology.Epidemiology.SIR
