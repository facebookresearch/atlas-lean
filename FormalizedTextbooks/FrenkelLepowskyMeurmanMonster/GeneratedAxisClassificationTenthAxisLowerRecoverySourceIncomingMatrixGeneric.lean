/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot02Packet

/-! Ungated exact original incoming matrix binding. No representative orientation is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete original incoming rational matrix uses the actual canonical spatial source word.
Its conjugation contains the spatial representative twice, so its sign has no effect. -/
def generatedTenthSourceIncomingMatrix : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalFifthRootMatrixQ 2

/-- The existing full actual local-word matrix theorem binds every original incoming coordinate.
No orientation of the chosen source fiber representative is asserted. -/
theorem generatedTenth_source_incoming_matrix_actual :
    generatedAxisGlobalFifthRoot02Packet.1 =
      generatedTenthSourceIncomingMatrix.map (Rat.castHom ℝ) := by
  have h := generatedAxisGlobalFifthRootMatrixQ_actual 2
  rw [generatedAxisGlobalFifthRoot02Packet_actual] at h
  exact h

/-- Every one of the576 original matrix entries has its exact rational source value. -/
theorem generatedTenth_source_incoming_matrix_entry (i j : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.1 i j =
      (generatedTenthSourceIncomingMatrix i j : ℝ) := by
  have h := congrFun (congrFun generatedTenth_source_incoming_matrix_actual i) j
  simpa only [Matrix.map_apply, Rat.coe_castHom] using h

/-- A future literal rational cache requires equality with the entire actual source matrix. -/
theorem generatedTenth_source_incoming_matrix_literal
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hM : ∀ i j, M i j = generatedTenthSourceIncomingMatrix i j) (i j : Fin 24) :
    generatedAxisGlobalFifthRoot02Packet.1 i j = (M i j : ℝ) := by
  rw [hM i j]
  exact generatedTenth_source_incoming_matrix_entry i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
