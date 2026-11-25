/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.ExponentialColeHopf
import Mathlib.Tactic.NormNum

/-! # Usage tests for classical exponential-sum Cole–Hopf solutions -/

open ColeHopf
open scoped ContDiff

-- A genuinely nonconstant two-mode profile, with denominator 1 + exp(t + x).
example (t x : ℝ) :
    deriv (fun t => exponentialSolution Finset.univ (fun _ : Fin 2 => 1)
      (fun i => (i.val : ℝ)) 1 t x) t +
      exponentialSolution Finset.univ (fun _ : Fin 2 => 1) (fun i => (i.val : ℝ)) 1 t x *
        deriv (exponentialSolution Finset.univ (fun _ : Fin 2 => 1)
          (fun i => (i.val : ℝ)) 1 t) x =
      iteratedDeriv 2 (exponentialSolution Finset.univ (fun _ : Fin 2 => 1)
        (fun i => (i.val : ℝ)) 1 t) x := by
  simpa using exponentialSolution_burgers_of_nonneg Finset.univ
    (fun _ : Fin 2 => (1 : ℝ)) (fun i => (i.val : ℝ)) 1
    (by simp) ⟨0, by simp, by norm_num⟩ t x

-- A nonzero denominator is a real restriction, even for a nonempty family.
example : heatMoment Finset.univ (fun i : Fin 2 => if i = 0 then 1 else -1)
    (fun i => (i.val : ℝ)) 1 0 0 0 = 0 := by
  norm_num [heatMoment, Fin.sum_univ_two]

-- The zero-viscosity transform is the zero solution.
example {ι : Type*} (s : Finset ι) (c k : ι → ℝ) (t x : ℝ) :
    exponentialSolution s c k 0 t x = 0 := by
  simp [exponentialSolution]

-- Check the actual heat equation, independently of the quotient calculation.
example (ν t x : ℝ) :
    deriv (fun t => heatMoment Finset.univ (fun _ : Fin 2 => 1)
      (fun i => (i.val : ℝ)) ν 0 t x) t =
    ν * iteratedDeriv 2 (heatMoment Finset.univ (fun _ : Fin 2 => 1)
      (fun i => (i.val : ℝ)) ν 0 t) x :=
  heatMoment_heat _ _ _ _ _ _

-- Nonunit viscosity: at the origin u = -2, u_x = -1, u_t = -2 and u_xx = 0.
private noncomputable def twoMode :=
  exponentialSolution Finset.univ (fun _ : Fin 2 => 1) (fun i => (i.val : ℝ)) 2

example : twoMode 0 0 = -2 := by
  norm_num [twoMode, exponentialSolution, heatMoment, Fin.sum_univ_two]

example : deriv (twoMode 0) 0 = -1 := by
  have h := (exponentialSolution_hasDerivAt_x Finset.univ
    (fun _ : Fin 2 => 1) (fun i => (i.val : ℝ)) 2 0 0
    (by norm_num [heatMoment, Fin.sum_univ_two])).deriv
  norm_num [heatMoment, Fin.sum_univ_two] at h
  exact h

example : deriv (fun t => twoMode t 0) 0 = -2 := by
  have h := (exponentialSolution_hasDerivAt_t Finset.univ
    (fun _ : Fin 2 => 1) (fun i => (i.val : ℝ)) 2 0 0
    (by norm_num [heatMoment, Fin.sum_univ_two])).deriv
  norm_num [heatMoment, Fin.sum_univ_two] at h
  exact h

example : iteratedDeriv 2 (twoMode 0) 0 = 0 := by
  have h := exponentialSolution_iteratedDeriv_two Finset.univ
    (fun _ : Fin 2 => 1) (fun i => (i.val : ℝ)) 2 0 0
    (by norm_num [heatMoment, Fin.sum_univ_two])
  norm_num [heatMoment, Fin.sum_univ_two] at h
  exact h

-- Unequal weights move away from the inflection point, exercising nonzero curvature.
example : iteratedDeriv 2
    (exponentialSolution Finset.univ (fun i : Fin 2 => (i.val : ℝ) + 1)
      (fun i => (i.val : ℝ)) 1 0) 0 = 4 / 27 := by
  have h := exponentialSolution_iteratedDeriv_two Finset.univ
    (fun i : Fin 2 => (i.val : ℝ) + 1) (fun i => (i.val : ℝ)) 1 0 0
    (by norm_num [heatMoment, Fin.sum_univ_two])
  norm_num [heatMoment, Fin.sum_univ_two] at h
  exact h

-- Negative denominator and negative frequency: no positivity assumption is hidden.
example (t x : ℝ) :
    deriv (fun t => exponentialSolution {()} (fun _ => -2) (fun _ => -3) 2 t x) t +
      exponentialSolution {()} (fun _ => -2) (fun _ => -3) 2 t x *
        deriv (exponentialSolution {()} (fun _ => -2) (fun _ => -3) 2 t) x =
      2 * iteratedDeriv 2 (exponentialSolution {()} (fun _ => -2) (fun _ => -3) 2 t) x := by
  apply exponentialSolution_burgers
  simp only [heatMoment, Finset.sum_singleton, pow_zero, mul_one]
  exact mul_ne_zero (by norm_num) (Real.exp_ne_zero _)

-- Empty support gives zero heat mass; it cannot satisfy nonvanishing.
example (ν t x : ℝ) : heatMoment (∅ : Finset ℕ) (fun _ => 1) (fun _ => 0) ν 0 t x = 0 := by
  simp [heatMoment]

-- Joint smoothness is exposed separately from a totalized derivative equality.
example (p : ℝ × ℝ) : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => twoMode q.1 q.2) p := by
  apply exponentialSolution_contDiffAt
  apply ne_of_gt
  exact heatMoment_zero_pos _ _ _ _ (by simp) ⟨0, by simp, by norm_num⟩ _ _

-- Initial data retains both the weights and the Cole–Hopf scaling.
example (x : ℝ) : twoMode 0 x = -4 * (Real.exp x / (1 + Real.exp x)) := by
  norm_num [twoMode, exponentialSolution, heatMoment, Fin.sum_univ_two]
