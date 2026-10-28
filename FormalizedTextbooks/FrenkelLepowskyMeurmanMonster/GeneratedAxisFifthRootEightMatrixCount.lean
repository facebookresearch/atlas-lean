/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightMatrixFlagOrbit

/-! Exact order of the whole original Conway matrix stabilizer from its four actual flag
orientations and its actual44352000 point stabilizers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual flag point stabilizer inside the complete original matrix stabilizer. -/
def generatedFifthRootEightMatrixPointStabilizer :
    Subgroup generatedFifthRootEightMatrixStabilizer :=
  MulAction.stabilizer generatedFifthRootEightMatrixStabilizer
    (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix)

/-- Inclusion into the original Conway group gives exactly the actual simultaneous flag
point stabilizer, with no extra membership condition. -/
theorem generatedFifthRootEight_matrix_point_map :
    generatedFifthRootEightMatrixPointStabilizer.map
      generatedFifthRootEightMatrixStabilizer.subtype =
        leechNormSixActualPairStabilizer
          generatedFifthRootEightNormFour generatedFifthRootEightNormSix := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a.val ∈ MulAction.stabilizer leechIsomSubgroup
      (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix)
    exact ha
  · intro hg
    let a : generatedFifthRootEightMatrixStabilizer :=
      ⟨g, generatedFifthRootEight_point_stabilizer_le hg⟩
    exact ⟨a, hg, rfl⟩

/-- The genuine nested point stabilizer has the actual flag stabilizer order. -/
theorem generatedFifthRootEight_matrix_point_card :
    Nat.card generatedFifthRootEightMatrixPointStabilizer = 44352000 := by
  rw [← Subgroup.card_subtype generatedFifthRootEightMatrixStabilizer
    generatedFifthRootEightMatrixPointStabilizer, generatedFifthRootEight_matrix_point_map,
    generatedFifthRootEight_point_stabilizer_card]

/-- The full original Conway matrix stabilizer has exactly177408000 elements, obtained from
actual orbit coverage and actual simultaneous point stabilizers. -/
theorem generatedFifthRootEight_matrix_stabilizer_card :
    Nat.card generatedFifthRootEightMatrixStabilizer = 177408000 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    generatedFifthRootEightMatrixStabilizer
    (generatedFifthRootEightNormFour, generatedFifthRootEightNormSix))
  rw [Nat.card_prod, generatedFifthRootEight_matrix_flag_orbit_card] at h
  change 4 * Nat.card generatedFifthRootEightMatrixPointStabilizer =
    Nat.card generatedFifthRootEightMatrixStabilizer at h
  rw [generatedFifthRootEight_matrix_point_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
