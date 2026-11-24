/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ExoticKnifePancake
import Mathlib.Tactic.Linarith

/-!
# Tests for lollipop intersections

The horizontal stem from the origin is tangent to the circle centered at $(7,3)$.
The opposite stem starts on the radius-five circle and crosses it a second time.
-/

namespace MetaMathlibExt.Lollipop

example : Real.cos (0 - Real.pi) < 0 := by
  let circ (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
    {x | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = r ^ 2}
  let stem (c : ℝ × ℝ) (r θ : ℝ) : Set (ℝ × ℝ) :=
    (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici r
  have htangent : stem (0, 0) 5 0 ∩ circ (7, 3) 3 = {(7, 0)} := by
    ext ⟨x, y⟩
    simp [circ, stem, Prod.ext_iff]
    constructor
    · rintro ⟨⟨_, rfl⟩, h⟩
      have hx : (x - 7) ^ 2 = 0 := by linarith
      exact ⟨by simpa [sub_eq_zero] using hx, rfl⟩
    · rintro ⟨rfl, rfl⟩
      norm_num
  have hsecant : stem (7, 3) 3 Real.pi ∩ circ (0, 0) 5 = {(4, 3), (-4, 3)} := by
    ext ⟨x, y⟩
    simp [circ, stem, Prod.ext_iff]
    constructor
    · rintro ⟨⟨_, _, _, rfl⟩, h⟩
      have hx : x ^ 2 = (4 : ℝ) ^ 2 := by linarith
      simpa using sq_eq_sq_iff_eq_or_eq_neg.mp hx
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨3, by norm_num⟩, by norm_num⟩
      · exact ⟨⟨11, by norm_num⟩, by norm_num⟩
  apply cos_sub_neg_of_lollipop_good_pair (0, 0) (7, 3) (r₁ := 5) (r₂ := 3)
    (by norm_num) (by norm_num) 0 Real.pi
  change (stem (0, 0) 5 0 ∩ circ (7, 3) 3).ncard +
    (stem (7, 3) 3 Real.pi ∩ circ (0, 0) 5).ncard ∈ _
  rw [htangent, hsecant, Set.ncard_singleton, Set.ncard_pair (by norm_num)]
  decide

end MetaMathlibExt.Lollipop
