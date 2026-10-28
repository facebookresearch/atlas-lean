/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhFrameOrbitWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagMonomialFrameCount

/-! The original intrinsic frame base and its genuine permutation invariance. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Intrinsic label 65 is precisely the original coordinate frame class. -/
theorem leechSeventhFrame_base_embedding :
    generatedAxisE8FrameRootEmbedding (generatedAxisE8FrameLabelBits 65) =
      leechReduction (leechCoordinateFrameLattice 0) := by
  let a : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, 1, 0]
  have ha : generatedAxisE8FrameLabelBits 65 = fun i => (a i : ZMod 2) := by decide +kernel
  rw [ha, generatedAxisE8FrameRootEmbedding_integer]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [← generatedFifthFrame_insert_root_sum]
  ext i
  fin_cases i <;> decide +kernel

/-- Every actual Golay permutation fixes the original coordinate frame class. -/
theorem leechSeventhFrame_permutation_fixed (p : golayAutomorphismSubgroup) :
    leechModTwoAction (golayPermutationIsometry p)
      (leechReduction (leechCoordinateFrameLattice 0)) =
        leechReduction (leechCoordinateFrameLattice 0) := by
  have hs : golaySignIsometry 0 = 1 := golaySignHom.map_one
  apply generatedFourthFlagMonomial_frame_fixed
  refine ⟨0, p, ?_⟩
  rw [hs, one_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
