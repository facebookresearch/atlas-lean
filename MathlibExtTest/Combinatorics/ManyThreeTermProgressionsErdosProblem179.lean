/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179

/-!
# Examples of three-term progression thresholds

The set of 0, 1, 2, and 4 has two three-term progressions with different common differences.
At cardinality zero the threshold for forcing a four-term progression is one.
-/

namespace MathlibExtTest.Combinatorics.ManyThreeTermProgressionsErdosProblem179

open MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

example : apCount {0, 1, 2, 4} 3 = 2 := by decide

example : ¬ HasAP {0, 1, 2, 4} 4 := by
  rintro ⟨a, d, hd, hall⟩
  have h₀ := hall 0 (by decide)
  have h₁ := hall 1 (by decide)
  have h₂ := hall 2 (by decide)
  have h₃ := hall 3 (by decide)
  simp at h₀ h₁ h₂ h₃
  omega

example : apThreshold 3 4 0 = 1 := by
  have hempty : ¬ HasAP ∅ 4 := by
    rintro ⟨a, d, hd, hall⟩
    simpa using hall 0 (by decide)
  unfold apThreshold
  apply IsLeast.csInf_eq
  constructor
  · intro A hA h
    obtain rfl := Finset.card_eq_zero.mp hA
    simp [apCount] at h
  · intro m hm
    by_contra! h
    exact hempty (hm ∅ rfl (by omega))

end MathlibExtTest.Combinatorics.ManyThreeTermProgressionsErdosProblem179
