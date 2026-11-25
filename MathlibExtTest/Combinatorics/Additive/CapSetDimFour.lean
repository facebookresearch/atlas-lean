/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Additive.CapSetDimFour

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

-- The maximum is attained.
example : ∃ s : Finset (Fin 4 → ZMod 3),
    s.card = 20 ∧ ThreeAPFree (s : Set (Fin 4 → ZMod 3)) := by
  obtain ⟨s, _, hcard, hs⟩ := addRothNumber_spec (Finset.univ : Finset (Fin 4 → ZMod 3))
  exact ⟨s, hcard.trans capSet_dim_four, hs⟩

-- At the next cardinality there is a progression with distinct first and middle terms.
example (s : Finset (Fin 4 → ZMod 3)) (hcard : s.card = 21) :
    ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, a + c = b + b ∧ a ≠ b := by
  by_contra! h
  have hs : ThreeAPFree (s : Set (Fin 4 → ZMod 3)) := by
    intro a ha b hb c hc habc
    exact h a ha b hb c hc habc
  have hle := hs.le_addRothNumber (Finset.subset_univ s)
  rw [hcard, capSet_dim_four] at hle
  omega

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
