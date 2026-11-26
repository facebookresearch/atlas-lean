/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Basic
import MathlibExt.Analysis.PDE.PoissonDirichlet

namespace MathlibExtTest.Analysis.PDE.PoissonDirichlet

open MeasureTheory
open scoped ContDiff ENNReal
open MathlibExt.Analysis.PDE.EllipticRegularityWanted
open MathlibExt.Analysis.SobolevMorreyWanted.Analysis.SobolevMorreyProblem (E partialDeriv)

private noncomputable abbrev interval : Set (E 1) := Metric.ball 0 1

-- Existence with a nonzero forcing on a nonempty bounded open set.
example : ∃ u : E 1 → ℝ, MemH10On interval u ∧
    IsWeakSolutionOn interval laplacianCoeff 0 0 (fun _ => 1) u := by
  have : IsFiniteMeasure (volume.restrict interval) :=
    ⟨by simpa [interval] using
      (measure_ball_lt_top (μ := (volume : Measure (E 1))) (x := 0) (r := 1))⟩
  obtain ⟨u, hu, hweak, _⟩ :=
    existsUnique_weakSolution_poisson (U := interval) (by decide)
      Metric.isOpen_ball Metric.isBounded_ball
      (memLp_const (1 : ℝ))
  exact ⟨u, hu, hweak⟩

-- The uniqueness clause identifies any homogeneous solution with zero.
example {w : E 1 → ℝ} (hw : MemH10On interval w)
    (hweak : IsWeakSolutionOn interval laplacianCoeff 0 0 0 w) :
    w =ᵐ[volume.restrict interval] 0 := by
  have hD (i : Fin 1) : IsWeakPartialDerivOn interval i 0 0 := by
    intro φ _
    simp
  have hz : MemH10On interval (0 : E 1 → ℝ) := by
    refine ⟨MemLp.zero, 0, fun i => ⟨MemLp.zero, hD i⟩, fun _ => 0, ?_, ?_, ?_⟩
    · intro k
      exact ⟨contDiff_zero_fun, HasCompactSupport.zero, by simp⟩
    · simp
    · intro i
      have hpartial : partialDeriv i (0 : E 1 → ℝ) = 0 := by
        funext x
        simp only [partialDeriv, fderiv_zero, Pi.zero_apply, zero_apply]
      simp [hpartial]
  have hzweak : IsWeakSolutionOn interval laplacianCoeff 0 0 0 0 := by
    refine ⟨MemLp.zero, 0, fun i => ⟨MemLp.zero, hD i⟩, fun φ _ => ?_⟩
    simp
  obtain ⟨u, _, _, hunique⟩ :=
    existsUnique_weakSolution_poisson (U := interval) (by decide)
      Metric.isOpen_ball Metric.isBounded_ball
      (f := (0 : E 1 → ℝ)) MemLp.zero
  exact (hunique w hw hweak).trans (hunique 0 hz hzweak).symm

end MathlibExtTest.Analysis.PDE.PoissonDirichlet
