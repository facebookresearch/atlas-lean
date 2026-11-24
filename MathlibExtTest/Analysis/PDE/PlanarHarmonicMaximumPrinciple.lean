/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple

import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Tests for the strong maximum principle for planar harmonic functions

The real part `Re z` is harmonic on the unit disc and not constant there, so by the strong maximum
principle it does not attain its maximum over the disc at the centre (nor anywhere in the disc).
-/

open InnerProductSpace Metric Set
open MathlibExt.Analysis.PDE.PlanarHarmonicMaximumPrinciple

example : ¬ IsMaxOn (fun z : ℂ => z.re) (ball 0 1) 0 := by
  intro hmax
  have hu : HarmonicOnNhd (fun z : ℂ => z.re) (ball 0 1) := fun z _ =>
    AnalyticAt.harmonicAt_re (f := id) (x := z) analyticAt_id
  have h := eqOn_of_isMaxOn_complex isOpen_ball (convex_ball 0 1).isPreconnected hu
    (mem_ball_self one_pos) hmax (show (1 / 2 : ℂ) ∈ ball 0 1 by
      rw [mem_ball, dist_zero_right]; norm_num)
  norm_num at h
