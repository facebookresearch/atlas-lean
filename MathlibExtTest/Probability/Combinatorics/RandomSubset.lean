/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Combinatorics.RandomSubset

@[expose] public section

open MeasureTheory unitInterval MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExtTest.Probability.Combinatorics.RandomSubset

/-- The empty set is always contained in the random subset. -/
example (p : Fin 4 → I) : (randomSubsetLaw p).real (containsEvent ∅) = 1 := by
  rw [randomSubsetLaw_real_containsEvent]
  simp

/-- With every element kept with probability `1/2`, a fixed pair is contained with probability
`1/4`. -/
example : (randomSubsetLaw (fun _ : Fin 4 => (⟨1 / 2, by norm_num, by norm_num⟩ : I))).real
    (containsEvent {0, 1}) = 1 / 4 := by
  rw [randomSubsetLaw_real_containsEvent]
  norm_num

/-- With element-dependent probabilities the containment probability is the product. -/
example (p : Fin 3 → I) :
    (randomSubsetLaw p).real (containsEvent {0, 2}) = (p 0 : ℝ) * p 2 := by
  rw [randomSubsetLaw_real_containsEvent]
  simp

/-- With every element kept with probability `1/2`, a fixed pair is avoided with probability
`1/4`. -/
example : (randomSubsetLaw (fun _ : Fin 4 => (⟨1 / 2, by norm_num, by norm_num⟩ : I))).real
    (avoidEvent {0, 1}) = 1 / 4 := by
  rw [randomSubsetLaw_real_avoidEvent]
  norm_num

/-- The events `S ⊆ R` are measurable. -/
example (S : Finset (Fin 5)) : MeasurableSet (containsEvent S) :=
  measurableSet_containsEvent S

end MathlibExtTest.Probability.Combinatorics.RandomSubset
