/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBall
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory Set
open scoped ContDiff Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted.Tests

-- A smooth bump in the radial variable gives admissible, nonzero data in dimension two.
private theorem exists_annular_bump :
    ∃ f : Rn 2 → ℝ, ContDiffOn ℝ ∞ f (ClosedUnitBall 2)ᶜ ∧ HasCompactSupport f ∧
      tsupport f ⊆ (ClosedUnitBall 2)ᶜ ∧ IsRadial f ∧ ∃ x, f x = 1 := by
  obtain ⟨g, hs, _, hg, _, h₃⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (Ioo_mem_nhds (show (2 : ℝ) < 3 by norm_num) (show (3 : ℝ) < 4 by norm_num))
  let f := fun x : Rn 2 => g ‖x‖
  have hring (x : Rn 2) (hx : x ∈ tsupport f) : ‖x‖ ∈ Ioo (2 : ℝ) 4 :=
    hs (tsupport_comp_subset_preimage g continuous_norm hx)
  refine ⟨f, ?_, ?_, ?_, fun _ _ h => congrArg g h, ?_⟩
  · intro x hx
    have hx₀ : x ≠ 0 := by
      rintro rfl
      exact hx (by simp [ClosedUnitBall])
    exact (hg.contDiffAt.comp x (contDiffAt_norm ℝ hx₀)).contDiffWithinAt
  · apply (isCompact_closedBall (0 : Rn 2) 4).of_isClosed_subset (isClosed_tsupport f)
    exact fun x hx => mem_closedBall_zero_iff.mpr (hring x hx).2.le
  · intro x hx (h : ‖x‖ ≤ 1)
    linarith [(hring x hx).1]
  · obtain ⟨x, hx⟩ := exists_norm_eq (Rn 2) (show 0 ≤ (3 : ℝ) by norm_num)
    exact ⟨x, by simpa [f, hx] using h₃⟩

-- Apply the infinite-exponent endpoint to that bump with the smallest permitted dimension.
example (p : ENNReal) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ f : Rn 2 → ℝ, (∃ x, f x = 1) ∧
      eLpNorm f ⊤ volume ≤ ENNReal.ofReal C *
        (eLpNorm f p volume + eLpNorm (fun x => ‖fderiv ℝ f x‖) p volume) := by
  obtain ⟨C, hC, h⟩ := exists_eLpNorm_le_sobolev_of_radial_of_tsupport_subset_compl_closedBall
    2 le_rfl p ⊤ hp1 hp2 le_top
  obtain ⟨f, hf, hc, hs, hr, hx⟩ := exists_annular_bump
  exact ⟨C, hC, f, hx, h f hf hc hs hr⟩

end MathlibExt.Analysis.FunctionalAnalysis.RadialSobolevExteriorBallWanted.Tests
