/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple
import MathlibExt.Analysis.PDE.RadialSymmetry

open InnerProductSpace Laplacian Metric Set
open scoped NNReal
open MathlibExt.Analysis.PDE.LaplaceMaximumPrinciple (laplacian_norm_sq)
open MathlibExt.Analysis.RadialSymmetryWanted.Analysis.PDE

namespace MathlibExtTest.Analysis.PDE.RadialSymmetry

private abbrev E := EuclideanSpace ℝ (Fin 1)

private noncomputable def u : E → ℝ := fun x => 1 - ‖x‖ ^ 2

/-- Apply radial symmetry to the quadratic solution with constant right-hand side. -/
example : ∃ v : ℝ → ℝ≥0, StrictAntiOn v (Icc (0 : ℝ) 1) ∧ v 0 = 1 ∧ v 1 = 0 := by
  have hC : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hu : ContDiff ℝ 2 u := contDiff_const.sub hC
  have hPDE : SolvesSemilinearPoisson (fun _ => 2) u := by
    constructor
    · intro x _
      change -Δ ((fun _ : E => (1 : ℝ)) - fun y : E => ‖y‖ ^ 2) x = 2
      rw [ContDiffAt.laplacian_sub contDiffAt_const hC.contDiffAt, laplacian_const,
        laplacian_norm_sq, finrank_euclideanSpace_fin]
      norm_num
    · intro x hx
      have hnorm : ‖x‖ = 1 := by simpa [mem_sphere] using hx
      simp [u, hnorm]
  have hpos : ∀ x ∈ ball (0 : E) 1, 0 < u x := by
    intro x hx
    have hnorm : ‖x‖ < 1 := by simpa [mem_ball] using hx
    change 0 < 1 - ‖x‖ ^ 2
    nlinarith [norm_nonneg x]
  obtain ⟨v, hdec, hprofile⟩ := semilinear_poisson_radial_symmetry (hn := by decide)
    u ⟨0, LipschitzWith.const 2⟩ hu.contDiffOn hPDE hpos
  let e : E := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one (0 : Fin 1)
  have heB : e ∈ closedBall (0 : E) 1 := by simp [mem_closedBall, he]
  refine ⟨v, hdec, NNReal.eq ?_, NNReal.eq ?_⟩
  · simpa [u] using (hprofile 0 (mem_closedBall_self zero_le_one)).symm
  · simpa [u, he] using (hprofile e heB).symm

end MathlibExtTest.Analysis.PDE.RadialSymmetry
