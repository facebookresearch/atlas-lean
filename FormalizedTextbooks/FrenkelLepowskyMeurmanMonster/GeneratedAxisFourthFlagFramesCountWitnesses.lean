/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesCountActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionFrameOrbit

/-! Actual integral witnesses and their 63 distinct lattice-quotient frame classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual integral image of the coordinate frame under its recorded physical word. -/
def generatedFourthFlagFramesCountWitness (j : Fin 63) : leechIntegral :=
  leechIntegralAction (generatedFourthFlagFramesCountIsometry j) (leechCoordinateFrameLattice 8)

/-- Every stored integer vector is the actual lattice image of its recorded word. -/
theorem generatedFourthFlagFramesCount_witness_coordinates (j : Fin 63) :
    (generatedFourthFlagFramesCountWitness j).val = generatedFourthFlagFramesCountVector j := by
  suffices h : ∀ n (hn : n < 63),
      (generatedFourthFlagFramesCountWitness ⟨n, hn⟩).val =
        generatedFourthFlagFramesCountVector ⟨n, hn⟩ from h j.val j.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    let j : Fin 63 := ⟨n, hn⟩
    change (generatedFourthFlagFramesCountWitness j).val = generatedFourthFlagFramesCountVector j
    by_cases hz : j = 0
    · rw [hz]
      change (leechIntegralAction 1 (leechCoordinateFrameLattice 8)).val = _
      rw [map_one]
      change leechCoordinateFrameVector 8 = generatedFourthFlagFramesCountVector 0
      decide +kernel
    · have hp := generatedFourthFlagFramesCount_parent_lt j hz
      have hparent := ih (generatedFourthFlagFramesCountParent j).val hp
        (generatedFourthFlagFramesCountParent j).isLt
      have hd := generatedFourthFlagFramesCount_action_double
        (generatedFourthFlagFramesCountLetter j)
        (generatedFourthFlagFramesCountWitness (generatedFourthFlagFramesCountParent j))
      rw [hparent, generatedFourthFlagFramesCount_edge_certificate j hz] at hd
      have hfactor : generatedFourthFlagFramesCountWitness j =
          leechIntegralAction (generatedFourthFlagFramesCountGenerator
            (generatedFourthFlagFramesCountLetter j))
            (generatedFourthFlagFramesCountWitness (generatedFourthFlagFramesCountParent j)) := by
        unfold generatedFourthFlagFramesCountWitness
        rw [generatedFourthFlagFramesCount_isometry_parent j hz, map_mul]
        rfl
      rw [hfactor]
      funext i
      have hi := congrFun hd i
      change 2 * _ = 2 * _ at hi
      omega

/-- The actual quotient class represented by the corresponding norm-eight lattice image. -/
def generatedFourthFlagFramesCountClass (j : Fin 63) : LeechModTwo :=
  leechReduction (generatedFourthFlagFramesCountWitness j)

/-- The checked literal parity vectors are the actual quotient coordinates of these witnesses. -/
theorem generatedFourthFlagFramesCount_class_coordinates (j : Fin 63) :
    leechModTwoLinearEquiv (generatedFourthFlagFramesCountClass j) =
      generatedFourthFlagFramesCountParity j := by
  rw [generatedFourthFlagFramesCountClass, leechModTwoLinearEquiv_reduce,
    ← monsterNortonLeechCoordinates_eq, generatedFourthFlagFramesCount_witness_coordinates]
  exact generatedFourthFlagFramesCount_parity_certificate j

/-- These 63 actual lattice-quotient classes are pairwise distinct. -/
theorem generatedFourthFlagFramesCount_class_injective :
    Function.Injective generatedFourthFlagFramesCountClass := by
  intro i j hij
  apply generatedFourthFlagFramesCount_parity_injective
  have h := congrArg leechModTwoLinearEquiv hij
  simpa only [generatedFourthFlagFramesCount_class_coordinates] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
