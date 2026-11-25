/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.XYOverNormSqDiscontinuity

/-!
# Continuity points of the explicit quotient

Real division gives the quotient its prescribed value at the origin. Away from the origin,
the open complement is a neighborhood, so continuity there is ordinary pointwise continuity.
-/

namespace MathlibExt.Analysis.Calculus.XYOverNormSqDiscontinuityWanted

example (p : ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ => q.1 * q.2 / (q.1 ^ 2 + q.2 ^ 2)) p ↔ p ≠ (0, 0) := by
  obtain ⟨hoff, horigin⟩ := continuousOn_compl_and_not_continuousAt_mul_div_sq_add_sq
    (fun q => q.1 * q.2 / (q.1 ^ 2 + q.2 ^ 2)) ⟨fun _ _ => rfl, by simp⟩
  constructor
  · rintro hc rfl
    exact horigin hc
  · intro hp
    exact hoff.continuousAt (isOpen_compl_singleton.mem_nhds hp)

end MathlibExt.Analysis.Calculus.XYOverNormSqDiscontinuityWanted
