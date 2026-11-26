/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: Muse Code powered by Meta Muse Spark
-/
module

public import MathlibExt.Analysis.Complex.Subharmonic.Nonpositive
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Angular lengths of strict sublevel sets

For any extended-real function `u`, real radius `r` and real threshold `K`,
the angular sublevel set consists of angles in `(0,2π]` at which
`u(circleMap 0 r θ) < -K`. Its length is the unnormalized Lebesgue measure
of that angle set. The circle has physical radius `|r|`; definitions also
include zero and negative `r` and arbitrary `K`.

Every such set lies in one full period, so its angular length is at most
`2π` and is finite. If `u` is upper semicontinuous on the open unit disk
and `|r| < 1`, the strict angular sublevel set is measurable. The radius
may be zero or negative, and the threshold has no positivity assumption.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Complex

/-- **Strict angular sublevel set on a zero-centered circle.** For any `u:ℂ→EReal` and real
`r,K`, define `S=(0,2π]∩{θ | u(r exp(iθ))<−(K:EReal)}`, where `r exp(iθ)=circleMap 0 r θ`
and the circle has center zero and physical radius `|r|`. The inequality is strict and `K`
need not be positive. At `r=0`, `S` is the full interval `(0,2π]` if `u(0)<−(K:EReal)`,
and is empty otherwise. No semicontinuity or measurability hypothesis is imposed by the
definition. -/
noncomputable def angularSublevelSet (u : ℂ → EReal) (r K : ℝ) : Set ℝ :=
  Set.Ioc 0 (2 * Real.pi) ∩
    {θ | u (circleMap 0 r θ) < -(K : EReal)}

/-- **Lebesgue angular length of a strict circular sublevel set.** For `u:ℂ→EReal` and
arbitrary real `r,K`, let `S=(0,2π]∩{θ | u(circleMap 0 r θ)<−(K:EReal)}`. Its angular
length is `ℓ=volume(S)∈ℝ≥0∞`, using unnormalized Lebesgue measure on the real angle
variable, not division by `2π` or physical arc length. The circle is centered at zero and
has radius `|r|`. At `r=0`, `ℓ=ENNReal.ofReal(2π)` when `u(0)<−(K:EReal)`, and `ℓ=0`
otherwise. -/
noncomputable def angularSublevelLength
    (u : ℂ → EReal) (r K : ℝ) : ℝ≥0∞ :=
  volume (angularSublevelSet u r K)

/-- Every angular sublevel set lies in the full-period interval `(0,2π]`.

```lean
theorem angularSublevelSet_subset (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelSet u r K ⊆ Set.Ioc 0 (2 * Real.pi)
``` -/
theorem angularSublevelSet_subset (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelSet u r K ⊆ Set.Ioc 0 (2 * Real.pi) :=
  Set.inter_subset_left

/-- Every strict angular sublevel set has length at most `2π`.

```lean
theorem angularSublevelLength_le (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelLength u r K ≤ ENNReal.ofReal (2 * Real.pi)
``` -/
theorem angularSublevelLength_le (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelLength u r K ≤ ENNReal.ofReal (2 * Real.pi) := by
  unfold angularSublevelLength
  calc volume (angularSublevelSet u r K)
      ≤ volume (Set.Ioc 0 (2 * Real.pi)) :=
        measure_mono (angularSublevelSet_subset u r K)
    _ = ENNReal.ofReal (2 * Real.pi) := by
        rw [Real.volume_Ioc]
        simp

/-- Every strict angular sublevel length is finite.

```lean
theorem angularSublevelLength_ne_top (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelLength u r K ≠ ⊤
``` -/
theorem angularSublevelLength_ne_top (u : ℂ → EReal) (r K : ℝ) :
    angularSublevelLength u r K ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (angularSublevelLength_le u r K)

/-- **Measurability of strict angular sublevel sets.** Let `u : ℂ → EReal` be upper
semicontinuous on the open unit disk. For real `r,K` with `|r| < 1`, the angles
`θ ∈ (0,2π]` satisfying `u(circleMap 0 r θ) < -K` form a measurable set.
Zero and negative radii are included, and the threshold `K` is arbitrary.

```lean
theorem measurableSet_angularSublevelSet
    {u : ℂ → EReal} {r K : ℝ}
    (hu : UpperSemicontinuousOn u (Metric.ball 0 1))
    (hr : |r| < 1) :
    MeasurableSet (angularSublevelSet u r K)
``` -/
theorem measurableSet_angularSublevelSet
    {u : ℂ → EReal} {r K : ℝ}
    (hu : UpperSemicontinuousOn u (Metric.ball 0 1))
    (hr : |r| < 1) :
    MeasurableSet (angularSublevelSet u r K) := by
  obtain ⟨U, hUopen, hU⟩ :=
    (upperSemicontinuousOn_iff_preimage_Iio.mp hu)
      (-(K : EReal))
  have hcircle (θ : ℝ) : circleMap 0 r θ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero]
    exact hr
  have hpre :
      {θ : ℝ | u (circleMap 0 r θ) < -(K : EReal)} =
        (circleMap 0 r) ⁻¹' U := by
    ext θ
    have h := Set.ext_iff.mp hU (circleMap 0 r θ)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio] at h
    simpa [hcircle θ] using h
  rw [angularSublevelSet, hpre]
  exact measurableSet_Ioc.inter
    (hUopen.measurableSet.preimage (measurable_circleMap 0 r))

end Complex
