/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Bernstein.Voronovskaya
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Tests for the Bernstein central moments and Voronovskaya's theorem: the `n = 1` moments by
hand, the moment bound, and Voronovskaya's limit for `f(t) = t ^ 2` and for affine `f`. -/

open Filter
open scoped unitInterval Topology

namespace MathlibExtTest.Analysis.SpecialFunctions.Bernstein.Voronovskaya

/-- The point `1/2` of the unit interval. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

example : (∑ k : Fin 3, ((half : ℝ) - bernstein.z k) * bernstein 2 k half) = 0 :=
  bernstein.mean two_ne_zero half

/-- For `n = 1` the fourth central moment is `x (1 - x) (1 - 3 x (1 - x))`; at `x = 1/2` it is
`1/16`. -/
example : (∑ k : Fin 2, ((half : ℝ) - bernstein.z k) ^ 4 * bernstein 1 k half) = 1 / 16 := by
  rw [bernstein.fourth_moment one_ne_zero half]
  norm_num [half]

example (x : I) : (∑ k : Fin 11, ((x : ℝ) - bernstein.z k) ^ 4 * bernstein 10 k x) ≤ 1 / 100 := by
  have := bernstein.fourth_moment_le (n := 10) (by norm_num) x
  norm_num at this ⊢
  exact this

/-- Voronovskaya for `f(t) = t ^ 2`: the limit is `x (1 - x)` (`f'' = 2`). -/
example (x : I) :
    Tendsto (fun n : ℕ => (n : ℝ) * (bernsteinApproximation n
        ((⟨fun t : ℝ => t ^ 2, continuous_pow 2⟩ : C(ℝ, ℝ)).restrict I) x -
          (x : ℝ) ^ 2)) atTop (𝓝 ((x : ℝ) * (1 - x))) := by
  have h := bernsteinApproximation.tendsto_voronovskaya (f := fun t : ℝ => t ^ 2)
    (by fun_prop) x
  have hd : deriv (deriv fun t : ℝ => t ^ 2) (x : ℝ) = 2 := by
    have : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := funext fun t => by
      simp
    rw [this]
    simp
  rw [hd] at h
  convert h using 2
  ring

/-- Affine functions are reproduced to first order: the limit vanishes. -/
example (a b : ℝ) (x : I) :
    Tendsto (fun n : ℕ => (n : ℝ) * (bernsteinApproximation n
        ((⟨fun t : ℝ => a * t + b, by fun_prop⟩ : C(ℝ, ℝ)).restrict I) x - (a * x + b)))
      atTop (𝓝 0) := by
  have h := bernsteinApproximation.tendsto_voronovskaya (f := fun t : ℝ => a * t + b)
    (by fun_prop) x
  have hd : deriv (deriv fun t : ℝ => a * t + b) (x : ℝ) = 0 := by
    have : deriv (fun t : ℝ => a * t + b) = fun _ => a := funext fun t =>
      (HasDerivAt.add_const b ((hasDerivAt_id' t).const_mul a)).deriv.trans (mul_one a)
    simp [this]
  rw [hd, mul_zero] at h
  exact h

end MathlibExtTest.Analysis.SpecialFunctions.Bernstein.Voronovskaya
