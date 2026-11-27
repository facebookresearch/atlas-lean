/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Normed.Module.RadialClip
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum

/-!
# Radial clipping of nonreal complex vectors

The actual real radial map fixes `(1/2)·i`, clips `2·i` to `i`, and has norm one
on that clipped value. These vectors have norms strictly below and above one.
The unit vector `i` is fixed, and the map is continuous on the complex plane.
-/

noncomputable section
open MathlibExt.Analysis.Normed.Module

namespace RadialClipConcreteSmoke

private def small : ℂ := (1 / 2 : ℝ) • Complex.I
private def large : ℂ := (2 : ℝ) • Complex.I

private theorem norm_small : ‖small‖ = (1 / 2 : ℝ) := by
  simp [small]

private theorem norm_large : ‖large‖ = (2 : ℝ) := by
  simp [large]

private theorem clip_large : radialClip large = Complex.I := by
  rw [radialClip, norm_large, max_eq_right (by norm_num : (1 : ℝ) ≤ 2)]
  change (2 : ℝ)⁻¹ • ((2 : ℝ) • Complex.I) = Complex.I
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]

example : ‖small‖ < 1 ∧ radialClip small = small := by
  refine ⟨?_, radialClip_eq_self ?_⟩ <;> rw [norm_small] <;> norm_num

example : 1 < ‖large‖ ∧ radialClip large = Complex.I ∧ ‖radialClip large‖ = 1 := by
  refine ⟨?_, clip_large, ?_⟩
  · rw [norm_large]
    norm_num
  · rw [clip_large, Complex.norm_I]

example : radialClip (Complex.I : ℂ) = Complex.I :=
  radialClip_eq_self (by rw [Complex.norm_I])

example : Continuous (radialClip : ℂ → ℂ) := continuous_radialClip

end RadialClipConcreteSmoke
