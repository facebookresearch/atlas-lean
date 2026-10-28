/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-source coset transitions and their resulting finite cover. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetChecked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetTargets
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCosetCover

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual original-source path representing a state in the proved transition cover. -/
noncomputable def y422CosetRepresentative (i : Fin 1080) : Y422Presentation :=
  y422TPathValue (y422CosetRoot i)

/-- The original empty path is the actual identity representative. -/
theorem y422CosetRepresentative_zero : y422CosetRepresentative 0 = 1 := by
  rw [y422CosetRepresentative, y422CosetRoot_zero, y422TPathValue_zero]

/-- Every state/source-generator transition is a proved coset fact in original C422/S/Q. -/
theorem y422CosetTransitions (i : Fin 1080) (a : Fin 9) :
    y522CosetRelation y422C322Subgroup
      (y422CosetRepresentative i * PresentedGroup.of a)
      (y422CosetRepresentative (y422CosetNext i a)) := by
  have h := y422CosetProgram_valid_original (y422CosetTransitionTarget i a)
  have hw := y422CosetTransitionWords_all i a
  change y422CosetWordValue (y422CosetProgram (y422CosetTransitionTarget i a)).1.left *
    (y422CosetWordValue (y422CosetProgram (y422CosetTransitionTarget i a)).1.right)⁻¹ ∈
      y422C322Subgroup at h
  rw [hw.1, hw.2, y422CosetWordValue_append, y422CosetPathWord_value,
    y422CosetWordValue_singleton, y422CosetGeneratorLetter_value,
    y422CosetPathWord_value] at h
  exact h

/-- Every original C422/S/Q element has one of these 1080 actual right-coset representatives. -/
theorem y422CosetRepresentative_cover (x : Y422Presentation) :
    ∃ i, y522CosetRelation y422C322Subgroup x (y422CosetRepresentative i) :=
  y555CosetCover_of_transitions (fun a => (PresentedGroup.of a : Y422Presentation))
    y422_generator_sq (PresentedGroup.closure_range_of y422Relations) y422C322Subgroup
    y422CosetRepresentative 0 y422CosetRepresentative_zero y422CosetNext
    y422CosetTransitions x

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
