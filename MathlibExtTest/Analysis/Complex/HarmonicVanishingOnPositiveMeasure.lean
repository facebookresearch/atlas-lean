/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasure
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open MeasureTheory MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted

-- A nonzero harmonic function can vanish on a line, but that line has zero outer measure.
example : volume {z : ℂ | z.re = 0} = 0 := by
  by_contra hne
  have hh : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => z.re) Set.univ :=
    fun z _ => AnalyticAt.harmonicAt_re (analyticAt_id : AnalyticAt ℂ (id : ℂ → ℂ) z)
  have hzero := eq_zero_of_harmonicOnNhd_of_vanishing_on_pos_volume Set.univ (fun z : ℂ => z.re)
    isOpen_univ isConnected_univ hh
    ⟨{z : ℂ | z.re = 0}, Set.subset_univ _, bot_lt_iff_ne_bot.mpr hne, fun _ hz => hz⟩
    (1 : ℂ) (Set.mem_univ _)
  simp at hzero
