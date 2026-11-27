/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDeriv
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.Connected

open MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted
open Metric Set

-- On the disc of radius one half the sharp derivative norm is two, attained by dilation.
example : ∃ g ∈ AdmissibleFamily (ball 0 (1 / 2)), ‖deriv g 0‖ = 2 := by
  let Ω := ball (0 : ℂ) (1 / 2)
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨g, hg, hmax⟩ := exists_mem_admissibleFamily_norm_deriv_eq_sSup Ω isOpen_ball
    (isConnected_ball hr) (mem_ball_self hr) (ball_subset_ball (by norm_num))
  refine ⟨g, hg, hmax.trans (IsGreatest.csSup_eq ⟨?_, ?_⟩)⟩
  · have hd (x : ℂ) : HasDerivAt (fun z : ℂ => 2 * z) 2 x := by
      simpa using (hasDerivAt_id' x).const_mul 2
    refine ⟨fun z => 2 * z, ⟨fun x _ => (hd x).differentiableAt.differentiableWithinAt,
      fun _ _ _ _ h => mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h, mul_zero _, ?_⟩, ?_⟩
    · intro z hz
      have hz' := mem_ball_zero_iff.mp hz
      rw [unitDisk, mem_ball_zero_iff, norm_mul]
      norm_num
      linarith
    · change ‖deriv (fun z : ℂ => 2 * z) 0‖ = 2
      rw [(hd 0).deriv]
      norm_num
  · rintro _ ⟨f, hf, rfl⟩
    have hm : MapsTo f Ω (closedBall (f 0) 1) := by
      rw [hf.2.2.1]
      exact fun z hz => ball_subset_closedBall (hf.2.2.2 hz)
    calc ‖deriv f 0‖ ≤ 1 / (1 / 2) := Complex.norm_deriv_le_div_of_mapsTo_ball hf.1 hm hr
      _ = 2 := by norm_num
