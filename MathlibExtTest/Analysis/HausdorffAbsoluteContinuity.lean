/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Analysis.HausdorffAbsoluteContinuity

open MeasureTheory
open MathlibExt.Analysis.HausdorffAbsoluteContinuityWanted.Analysis.HausdorffAbsoluteContinuity

namespace HausdorffAbsoluteContinuityTest

-- In dimension zero the cube is a single point, and the reference measure is a probability.
example : ∃ C : ℝ, ∀ k n : Fin 0 → ℕ, k ≤ n →
    diff (momentOf (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))) k n ≤
      C * diff (momentOf (volume.restrict (cube 0))) k n := by
  have hcube : cube 0 = Set.univ := by
    ext x
    simp [cube]
  apply (hausdorff_absolute_continuity (Measure.dirac 0) (by simp [hcube])).mp
  refine ⟨1, ?_⟩
  simp [hcube, volume_euclideanSpace_eq_dirac]

-- In positive dimension an atom at a corner prevents a uniform bound on the differences.
example : ¬ ∃ C : ℝ, ∀ k n : Fin 1 → ℕ, k ≤ n →
    diff (momentOf (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1)))) k n ≤
      C * diff (momentOf (volume.restrict (cube 1))) k n := by
  let x : EuclideanSpace ℝ (Fin 1) := 0
  have hx : x ∈ cube 1 := by simp [cube, x]
  have hμ : Measure.dirac x (cube 1)ᶜ = 0 := by
    simp [Measure.dirac_apply, hx]
  intro h
  obtain ⟨C, hC⟩ := (hausdorff_absolute_continuity (Measure.dirac x) hμ).mpr h
  have hmass := hC ({x} : Set (EuclideanSpace ℝ (Fin 1)))
  have hzero : (volume : Measure (EuclideanSpace ℝ (Fin 1))) {x} = 0 := measure_singleton x
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton x), smul_apply,
    Measure.restrict_apply (measurableSet_singleton _), Set.singleton_inter_of_mem hx,
    hzero, smul_zero] at hmass
  exact (not_le_of_gt zero_lt_one) hmass

end HausdorffAbsoluteContinuityTest
