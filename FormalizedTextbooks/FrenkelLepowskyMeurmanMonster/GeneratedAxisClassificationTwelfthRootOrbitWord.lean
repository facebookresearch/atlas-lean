/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRootOrbitData

/-! Every finite root-orbit witness is a whole word in the actual original section isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual root-line action of an original section generator is its proved source dictionary. -/
theorem generatedTwelfth_root_generator_actual (g : Fin 18) (r : Fin 120) :
    leechSeventhE8SectionRootIndex (generatedAxisE8FrameSystemOrbitLetter g) r =
      leechSeventhE8RootImage g r := by
  apply leechSeventhE8RootLabel_injective
  rw [leechSeventhE8SectionRootIndex_label]
  exact leechSeventhE8Root_label_action g r

/-- Original section-generator letters retain their genuine group inverses. -/
def generatedTwelfthRootOrbitLetter (l : Fin 18 × Bool) : leechSeventhE8SectionGroup :=
  if l.2 then (generatedAxisE8FrameSystemOrbitLetter l.1)⁻¹
  else generatedAxisE8FrameSystemOrbitLetter l.1

/-- Every finite original positive and inverse letter is the actual whole root permutation. -/
theorem generatedTwelfth_root_orbit_letter_actual (l : Fin 18 × Bool) (r : Fin 120) :
    leechSeventhE8SectionRootIndex (generatedTwelfthRootOrbitLetter l) r =
      generatedTwelfthRootFiniteLetter l r := by
  rcases l with ⟨g, b⟩
  cases b
  · exact generatedTwelfth_root_generator_actual g r
  · change generatedTwelfthRootAction (generatedAxisE8FrameSystemOrbitLetter g)⁻¹ r = _
    rw [map_inv]
    apply (generatedTwelfthRootAction (generatedAxisE8FrameSystemOrbitLetter g)).injective
    change generatedTwelfthRootAction (generatedAxisE8FrameSystemOrbitLetter g)
        ((generatedTwelfthRootAction (generatedAxisE8FrameSystemOrbitLetter g)).symm r) =
      generatedTwelfthRootAction (generatedAxisE8FrameSystemOrbitLetter g)
        (generatedTwelfthRootFiniteBackward g r)
    rw [Equiv.apply_symm_apply]
    change r = leechSeventhE8SectionRootIndex (generatedAxisE8FrameSystemOrbitLetter g) _
    rw [generatedTwelfth_root_generator_actual, generatedTwelfth_root_finite_inverse]

/-- Complete original section words have exactly their original full finite root evaluation. -/
theorem generatedTwelfth_root_orbit_word_actual (w : List (Fin 18 × Bool)) (r : Fin 120) :
    leechSeventhE8SectionRootIndex ((w.map generatedTwelfthRootOrbitLetter).prod) r =
      w.foldr generatedTwelfthRootFiniteLetter r := by
  induction w generalizing r with
  | nil => exact generatedTwelfth_root_index_one r
  | cons l w ih =>
    change leechSeventhE8SectionRootIndex
      (generatedTwelfthRootOrbitLetter l * (w.map generatedTwelfthRootOrbitLetter).prod) r = _
    rw [generatedTwelfth_root_index_mul, ih, generatedTwelfth_root_orbit_letter_actual]
    rfl

/-- Every displayed witness is an entire word in the full genuine original section group. -/
def generatedTwelfthRootOrbitWitness (n : Fin 235) : leechSeventhE8SectionGroup :=
  ((generatedTwelfthRootOrbitWitnessWord n).map generatedTwelfthRootOrbitLetter).prod

/-- Every witness coordinate is the complete actual original group action on that root line. -/
theorem generatedTwelfth_root_orbit_witness_actual (n : Fin 235) (r : Fin 120) :
    generatedTwelfthRootAction (generatedTwelfthRootOrbitWitness n) r =
      generatedTwelfthRootOrbitFiniteWord n r :=
  generatedTwelfth_root_orbit_word_actual (generatedTwelfthRootOrbitWitnessWord n) r

/-- Each genuine witness fixes every preceding original root line of its level. -/
theorem generatedTwelfth_root_orbit_actual_prefix (k : Fin 6)
    (j : Fin (generatedTwelfthRootOrbitBound k)) (r : Fin 120) (hr : r.val < k.val) :
    generatedTwelfthRootAction
      (generatedTwelfthRootOrbitWitness (generatedTwelfthRootOrbitWitnessNumber k j)) r = r := by
  rw [generatedTwelfth_root_orbit_witness_actual]
  exact generatedTwelfth_root_orbit_witness_prefix k j r hr

/-- Each full genuine source word has its distinct certified root-orbit target. -/
theorem generatedTwelfth_root_orbit_actual_target (k : Fin 6)
    (j : Fin (generatedTwelfthRootOrbitBound k)) :
    generatedTwelfthRootAction
        (generatedTwelfthRootOrbitWitness (generatedTwelfthRootOrbitWitnessNumber k j))
        (Fin.castLE (by decide : 6 ≤ 120) k) =
      generatedTwelfthRootOrbitTarget (generatedTwelfthRootOrbitWitnessNumber k j) := by
  rw [generatedTwelfth_root_orbit_witness_actual]
  exact generatedTwelfth_root_orbit_witness_target k j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
