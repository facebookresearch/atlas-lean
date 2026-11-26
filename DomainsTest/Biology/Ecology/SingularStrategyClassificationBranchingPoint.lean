/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.SingularStrategyClassificationBranchingPoint
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tests for evolutionary branching points

The quadratic invasion fitness `s x y = (y - x) * (y - 2 * x)` has singular strategy
`x* = 0` with `s_xy = -3` and `s_yy = 2`: convergence-stable but not ESS-stable. The tests
use the diagonal identity to recover `s_xx = 4`, check that the fitness gradient has derivative
`-1` at `x*`, and apply `branchingPoint` to obtain mutual invasibility.
-/

namespace DomainsTest.Biology.Ecology.SingularStrategyClassificationBranchingPoint

open WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

/-- The `y`-derivative of the test fitness at `y = 0`, as a function of the resident `x`. -/
private theorem deriv_slice_test (x : ℝ) :
    deriv (fun y : ℝ => (y - x) * (y - 2 * x)) 0 = -3 * x := by
  have hA : HasDerivAt (fun y : ℝ => y - x) 1 0 := (hasDerivAt_id' 0).sub_const x
  have hB : HasDerivAt (fun y : ℝ => y - 2 * x) 1 0 := (hasDerivAt_id' 0).sub_const (2 * x)
  have hM : HasDerivAt (fun y : ℝ => (y - x) * (y - 2 * x))
      (1 * (0 - 2 * x) + (0 - x) * 1) 0 := hA.mul hB
  rw [hM.deriv]
  ring

/-- The `y`-derivative of the test fitness at resident `0`, as a function of the mutant. -/
private theorem deriv_slice_test_zero (y : ℝ) :
    deriv (fun y' : ℝ => (y' - 0) * (y' - 2 * 0)) y = 2 * y := by
  have hA : HasDerivAt (fun y' : ℝ => y' - 0) 1 y := (hasDerivAt_id' y).sub_const 0
  have hB : HasDerivAt (fun y' : ℝ => y' - 2 * 0) 1 y := (hasDerivAt_id' y).sub_const (2 * 0)
  have hM : HasDerivAt (fun y' : ℝ => (y' - 0) * (y' - 2 * 0))
      (1 * (y - 2 * 0) + (y - 0) * 1) y := hA.mul hB
  rw [hM.deriv]
  ring

/-- The test fitness has singular strategy `x* = 0`. -/
private theorem test_isSingular :
    IsSingular (fun x y => (y - x) * (y - 2 * x)) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.2 - p.1) := contDiff_snd.sub contDiff_fst
    have h2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.2 - 2 * p.1) :=
      contDiff_snd.sub (contDiff_const.mul contDiff_fst)
    exact h1.mul h2
  · intro x
    simp
  · change deriv (fun y : ℝ => (y - 0) * (y - 2 * 0)) 0 = 0
    rw [deriv_slice_test_zero]
    ring

/-- The mixed partial of the test fitness at `(0, 0)` is `-3`. -/
private theorem test_sxy :
    sxy (fun x y => (y - x) * (y - 2 * x)) 0 0 = -3 := by
  change deriv (fun x : ℝ => deriv (fun y => (y - x) * (y - 2 * x)) 0) 0 = -3
  have hslice : (fun x : ℝ => deriv (fun y => (y - x) * (y - 2 * x)) 0)
      = fun x => -3 * x :=
    funext deriv_slice_test
  rw [hslice]
  exact (hasDerivAt_const_mul (-3)).deriv

/-- The mutant second partial of the test fitness at `(0, 0)` is `2`. -/
private theorem test_syy :
    syy (fun x y => (y - x) * (y - 2 * x)) 0 0 = 2 := by
  change deriv (fun y : ℝ => deriv (fun y' => (y' - 0) * (y' - 2 * 0)) y) 0 = 2
  have hinner : (fun y : ℝ => deriv (fun y' => (y' - 0) * (y' - 2 * 0)) y)
      = fun y => 2 * y :=
    funext deriv_slice_test_zero
  rw [hinner]
  exact (hasDerivAt_const_mul 2).deriv

-- The two nonzero off-diagonal terms in the Hessian contribute to the resident curvature.
example : sxx (fun x y => (y - x) * (y - 2 * x)) 0 0 = 4 := by
  have h := (diagonal_identity_and_hasDerivAt test_isSingular).1
  rw [test_sxy, test_syy] at h
  linarith only [h]

-- The mixed and mutant curvatures contribute to the slope of the fitness gradient.
example : HasDerivAt (fitnessGradient (fun x y => (y - x) * (y - 2 * x))) (-1) 0 := by
  have h := (diagonal_identity_and_hasDerivAt test_isSingular).2
  have hs : (-3 : ℝ) + 2 = -1 := by ring
  rwa [test_sxy, test_syy, hs] at h

/-- The test fitness is convergence-stable (`-3 + 2 < 0`) but not ESS-stable (`0 < 2`), so
`branchingPoint` applies to it. -/
theorem test_branchingPoint :
    ∃ δ > 0, (∀ x, 0 < |x - 0| → |x - 0| < δ →
        0 < (0 - x) * fitnessGradient (fun x y => (y - x) * (y - 2 * x)) x) ∧
      (∀ y, 0 < |y - 0| → |y - 0| < δ →
        0 < (fun x y => (y - x) * (y - 2 * x)) 0 y) ∧
      ∀ e, 0 < e → e < δ →
        0 < (fun x y => (y - x) * (y - 2 * x)) (0 - e) (0 + e) ∧
        0 < (fun x y => (y - x) * (y - 2 * x)) (0 + e) (0 - e) := by
  have hconv : sxy (fun x y => (y - x) * (y - 2 * x)) 0 0
      + syy (fun x y => (y - x) * (y - 2 * x)) 0 0 < 0 := by
    linarith [test_sxy, test_syy]
  have hyy : 0 < syy (fun x y => (y - x) * (y - 2 * x)) 0 0 := by
    linarith [test_syy]
  exact branchingPoint test_isSingular hconv hyy

/-- For the test fitness, strategies at equal distance on either side of `0` invade each other. -/
theorem test_mutual_invade :
    ∃ δ > 0, ∀ (e : ℝ), 0 < e → e < δ →
      0 < (fun x y => (y - x) * (y - 2 * x)) (-e) e ∧
      0 < (fun x y => (y - x) * (y - 2 * x)) e (-e) := by
  obtain ⟨δ, hδ, -, -, hmut⟩ := test_branchingPoint
  refine ⟨δ, hδ, fun e he0 heδ => ?_⟩
  have h := hmut e he0 heδ
  simpa using h

end DomainsTest.Biology.Ecology.SingularStrategyClassificationBranchingPoint
