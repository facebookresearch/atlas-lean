/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.ScalingFunction

/-!
# Tests for the scaling function

At index zero the basis recovers the unit-norm generator. At index minus one it gives the
translate by one unit to the left, orthogonal to the generator.
-/

open MeasureTheory
open scoped InnerProductSpace
open MathlibExt.Analysis.Wavelet.Multiresolution
open MathlibExt.Analysis.Wavelet.MultiresolutionWanted

example {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ φ g : V 0, ‖φ‖ = 1 ∧ ⟪φ, g⟫_ℂ = 0 ∧
      ⇑(g : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
        fun x => (φ : Lp ℂ 2 (volume : Measure ℝ)) (x + 1) := by
  obtain ⟨φ, b, hb⟩ := exists_scaling_function hV
  have h0 : (b 0).val = φ := Lp.ext (by simpa only [Int.cast_zero, sub_zero] using hb 0)
  refine ⟨b 0, b (-1), b.orthonormal.1 0, b.orthonormal.2 (by decide), ?_⟩
  rw [h0]
  simpa using hb (-1)
