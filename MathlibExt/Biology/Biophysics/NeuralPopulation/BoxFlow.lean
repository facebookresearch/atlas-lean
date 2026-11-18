/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# Box clipping projection

Coordinatewise clipping onto an interval lands in the interval, is the identity inside it, and is idempotent: clipped trajectories started in the box see the original field.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow

/-- The coordinatewise clipping projection onto the box
`[0, U]`: `clip U x = max 0 (min U x)`. -/
def clipBox (U : ℝ) (x : ℝ) : ℝ :=
  max 0 (min U x)

/-- **Clipping lands in the box.** For `0 ≤ U`, every clipped
value lies in `[0, U]`. -/
theorem clipBox_mem {U x : ℝ} (hU : 0 ≤ U) :
    0 ≤ clipBox U x ∧ clipBox U x ≤ U := by
  unfold clipBox
  exact ⟨le_max_left 0 (min U x), max_le hU (min_le_left U x)⟩

/-- **Clipping is the identity inside the box.** For a value
already in `[0, U]`, clipping does not change it; hence clipped
trajectories started in the box use the original field values. -/
theorem clipBox_eq_of_mem {U x : ℝ} (h0 : 0 ≤ x) (hU : x ≤ U) :
    clipBox U x = x := by
  unfold clipBox
  rw [min_eq_right hU, max_eq_right h0]

/-- **Clipping is idempotent.** Clipping a clipped value changes
nothing. -/
theorem clipBox_idempotent {U x : ℝ} (hU : 0 ≤ U) :
    clipBox U (clipBox U x) = clipBox U x := by
  have h := clipBox_mem hU (x := x)
  exact clipBox_eq_of_mem h.1 h.2


end MathlibExt.Biology.Biophysics.NeuralPopulation.BoxFlow
