/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.IteratedDerivPartial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

open scoped ContDiff

-- A finite Cn hypothesis suffices; joint smoothness is not needed for a single order.
example {q : ℝ → ℝ → ℝ} {n : ℕ} (hq : ContDiff ℝ n (Function.uncurry q)) (t x : ℝ) :
    iteratedDeriv n (q t) x =
      iteratedFDeriv ℝ n (Function.uncurry q) (t,x) (fun _ => (0,1)) :=
  hq.iteratedDeriv_snd_eq_iteratedFDeriv (t,x)

-- The norm estimate has coefficient one, including order zero.
example {q : ℝ → ℝ → ℝ} {n : ℕ} (hq : ContDiff ℝ n (Function.uncurry q)) (t x : ℝ) :
    ‖iteratedDeriv n (q t) x‖ ≤ ‖iteratedFDeriv ℝ n (Function.uncurry q) (t,x)‖ :=
  hq.norm_iteratedDeriv_snd_le (t,x)

example {q : ℝ → ℝ → ℝ} (hq : ContDiff ℝ 0 (Function.uncurry q)) (t x : ℝ) :
    q t x = iteratedFDeriv ℝ 0 (Function.uncurry q) (t,x) (fun _ => (0,1)) := by
  simpa only [iteratedDeriv_zero] using hq.iteratedDeriv_snd_eq_iteratedFDeriv (t,x)

-- A quadratic distinguishes a second derivative from a divided Taylor coefficient.
example (t x : ℝ) :
    iteratedFDeriv ℝ 2 (fun p : ℝ × ℝ => p.1 + p.2^2) (t,x) (fun _ => (0,1)) = 2 := by
  have hq : ContDiff ℝ 2 (Function.uncurry (fun t x : ℝ => t + x^2)) := by fun_prop
  have he := hq.iteratedDeriv_snd_eq_iteratedFDeriv (t,x)
  simp only [Function.uncurry_def] at he
  rw [← he]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have h1 : deriv (fun y : ℝ => t + y^2) = fun y => 2*y := by
    funext y
    simp
  rw [h1]
  simp

-- Actual spatial jets remain jointly smooth, with time dependence retained.
example (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv n (fun y => p.1 + y^2) p.2) := by
  have hq : ContDiff ℝ ∞ (Function.uncurry (fun t x : ℝ => t + x^2)) := by fun_prop
  exact hq.contDiff_iteratedDeriv_snd n
