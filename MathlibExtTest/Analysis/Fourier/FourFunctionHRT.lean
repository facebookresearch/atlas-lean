/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.FourFunctionHRT
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

open MeasureTheory Set
open MathlibExt.Analysis.FourFunctionHRTWanted

namespace MathlibExtTest.Analysis.Fourier.FourFunctionHRT

-- The conclusion includes relations in which the modulation coefficient vanishes.
example (g : ℝ → ℂ) (hg : MemLp g 2 volume) (hn : ¬(g =ᵐ[volume] 0)) (a b c : ℂ)
    (h : (fun x ↦ a * g x + b * g (x - 1) + c * g (x - Real.sqrt 2)) =ᵐ[volume] 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨ha, hb, hc, _⟩ := conjecture_holds g hg hn a b c 0 (by simpa using h)
  exact ⟨ha, hb, hc⟩

-- The indicator gives a concrete nonzero L² function to which the theorem applies.
private noncomputable def window : ℝ → ℂ := (Ioc 0 1).indicator (fun _ ↦ 1)

example : ¬((fun x ↦ modulationOne x * window x) =ᵐ[volume] window) := by
  have hLp : MemLp window 2 volume :=
    memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet 1 (.inr (by simp))
  have hn : ¬(window =ᵐ[volume] 0) := by
    intro h
    have hnull : volume (Ioc (0 : ℝ) 1) = 0 :=
      measure_mono_null (fun x hx ↦ by
        change window x ≠ 0
        simp [window, hx]) (ae_iff.mp h)
    simp at hnull
  intro h
  have hr := conjecture_holds window hLp hn (-1) 0 0 1 (by
    filter_upwards [h] with x hx
    simp [hx])
  exact one_ne_zero hr.2.2.2

end MathlibExtTest.Analysis.Fourier.FourFunctionHRT
