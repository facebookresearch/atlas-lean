/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Ecology.SingularStrategyClassificationConvergenceStableIffAndGradient
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Tests for convergence stability of singular strategies

On the concrete invasion fitness `s₀ x y = x (x - y)` with singular strategy `x* = 0`, the
second partial derivatives at `(0, 0)` are `s_xx = 2`, `s_xy = -1`, `s_yy = 0`, so both sides
of the convergence-stability equivalence hold; the fitness gradient is `D(x) = -x`, hence
`(0 - 1) D(1) = 1 > 0`.
-/

@[expose] public section

open WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

namespace DomainsTest.Biology.Ecology.SingularStrategyClassificationConvergenceStableIffAndGradient

/-- The concrete invasion fitness `s₀ x y = x (x - y)`. -/
private noncomputable def s0 (x y : ℝ) : ℝ := x * (x - y)

/-- `s₀` has singular strategy `0`: it is `C²`, vanishes on the diagonal, and `D(0) = 0`. -/
private lemma s0_singular : IsSingular s0 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (fun p : ℝ × ℝ => s0 p.1 p.2) = fun p : ℝ × ℝ => p.1 * (p.1 - p.2) := rfl
    rw [h]
    exact contDiff_fst.mul (contDiff_fst.sub contDiff_snd)
  · intro x
    simp [s0]
  · simp only [fitnessGradient]
    have heq : (fun y => s0 0 y) = fun _ => (0 : ℝ) := by
      funext y
      simp [s0]
    rw [heq]
    exact deriv_const _ _

/-- The fitness gradient of `s₀` is `D(x) = -x`. -/
private lemma s0_gradient (x : ℝ) : fitnessGradient s0 x = -x := by
  have h1 : HasDerivAt (fun y : ℝ => x - y) (0 - 1) x :=
    (hasDerivAt_const x x).sub (hasDerivAt_id x)
  have h1b : HasDerivAt (fun y : ℝ => x - y) (-1) x := by
    simpa using h1
  have h2 : HasDerivAt (fun y : ℝ => x * (x - y)) (x * (-1)) x := h1b.const_mul x
  have h3 : HasDerivAt (fun y : ℝ => s0 x y) (-x) x := by
    simpa [s0, mul_neg, mul_one] using h2
  exact h3.deriv

/-- For `s₀`, `s_yy = 0` at `(0, 0)`. -/
private lemma s0_syy : syy s0 0 0 = 0 := by
  have hinner : ∀ y, deriv (fun y' => s0 0 y') y = 0 := by
    intro y
    have heq : (fun y' => s0 0 y') = fun _ => (0 : ℝ) := by
      funext y'
      simp [s0]
    rw [heq]
    exact deriv_const _ _
  have houter : (fun y => deriv (fun y' => s0 0 y') y) = fun _ => (0 : ℝ) :=
    funext hinner
  simp [syy, houter]

/-- For `s₀`, `s_xy = -1` at `(0, 0)`. -/
private lemma s0_sxy : sxy s0 0 0 = -1 := by
  have hinner : ∀ x, deriv (fun y => s0 x y) 0 = -x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => x - y) (0 - 1) 0 :=
      (hasDerivAt_const 0 x).sub (hasDerivAt_id 0)
    have h1b : HasDerivAt (fun y : ℝ => x - y) (-1) 0 := by
      simpa using h1
    have h2 : HasDerivAt (fun y : ℝ => x * (x - y)) (x * (-1)) 0 := h1b.const_mul x
    have h3 : HasDerivAt (fun y : ℝ => s0 x y) (-x) 0 := by
      simpa [s0, mul_neg, mul_one] using h2
    exact h3.deriv
  have houter : (fun x => deriv (fun y => s0 x y) 0) = fun x => -x := funext hinner
  have hderiv : HasDerivAt (fun x : ℝ => -x) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  simp [sxy, houter, hderiv.deriv]

/-- For `s₀`, `s_xx = 2` at `(0, 0)`. -/
private lemma s0_sxx : sxx s0 0 0 = 2 := by
  have hinner : ∀ x, deriv (fun x' => s0 x' 0) x = 2 * x := by
    intro x
    have heq : (fun x' => s0 x' 0) = fun x' => x' * x' := by
      funext x'
      simp [s0]
    rw [heq]
    have h : HasDerivAt (fun x' : ℝ => x' * x') (1 * x + x * 1) x :=
      (hasDerivAt_id x).mul (hasDerivAt_id x)
    have h2 : HasDerivAt (fun x' : ℝ => x' * x') (2 * x) x := h.congr_deriv (by ring)
    exact h2.deriv
  have houter : (fun x => deriv (fun x' => s0 x' 0) x) = fun x => 2 * x := funext hinner
  have hderiv : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) 0 := (hasDerivAt_id (0 : ℝ)).const_mul 2
  have hderiv2 : HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by simpa using hderiv
  simp [sxx, houter, hderiv2.deriv]

/-- The convergence-stability equivalence holds for `s₀` at `0`. -/
example : sxy s0 0 0 + syy s0 0 0 < 0 ↔ syy s0 0 0 < sxx s0 0 0 :=
  (convergenceStable_iff_and_gradient s0_singular).1

/-- For `s₀` at `0`, `s_xy + s_yy = -1 < 0`. -/
example : sxy s0 0 0 + syy s0 0 0 < 0 := by
  rw [s0_sxy, s0_syy]
  norm_num

/-- For `s₀` at `0`, `s_yy = 0 < 2 = s_xx`. -/
example : syy s0 0 0 < sxx s0 0 0 := by
  rw [s0_syy, s0_sxx]
  norm_num

/-- For `s₀` at `0`, the fitness gradient points towards `0` near `0`. -/
example : ∃ δ > 0, ∀ x, 0 < |x - 0| → |x - 0| < δ → 0 < (0 - x) * fitnessGradient s0 x :=
  (convergenceStable_iff_and_gradient s0_singular).2 (by rw [s0_sxy, s0_syy]; norm_num)

/-- At `x = 1`, `(0 - 1) D(1) = 1 > 0`. -/
example : (0 - 1) * fitnessGradient s0 1 = 1 := by
  rw [s0_gradient]
  norm_num

end DomainsTest.Biology.Ecology.SingularStrategyClassificationConvergenceStableIffAndGradient
