/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual 720-element image lower bound for the original source A5 parabolic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3A5Source

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual subgroup image of the original five-generator A5 source parabolic. -/
def y322Orthogonal3A5Image : Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :=
  y322A5Parabolic.map y322Orthogonal3Hom

/-- A concrete original-source candidate regarded as an actual element of the A5 matrix image. -/
noncomputable def y322Orthogonal3A5ImageCandidate (i : Fin 720) : y322Orthogonal3A5Image :=
  ⟨y322Orthogonal3Hom (y322Orthogonal3A5SourceCandidate i),
    ⟨y322Orthogonal3A5SourceCandidate i, y322Orthogonal3A5SourceCandidate_mem i, rfl⟩⟩

/-- All 720 concrete source candidates have distinct actual finite image elements. -/
theorem y322Orthogonal3A5ImageCandidate_injective :
    Function.Injective y322Orthogonal3A5ImageCandidate := by
  intro i j hij
  apply y322Orthogonal3A5Code_injective
  have h := congrArg (fun x : y322Orthogonal3A5Image =>
    y322Orthogonal3MatrixCode x.val.val) hij
  change y322Orthogonal3MatrixCode
      (y322Orthogonal3Hom (y322Orthogonal3A5SourceCandidate i)).val =
    y322Orthogonal3MatrixCode (y322Orthogonal3Hom (y322Orthogonal3A5SourceCandidate j)).val at h
  rw [y322Orthogonal3A5SourceCandidate_matrix, y322Orthogonal3A5SourceCandidate_matrix] at h
  have hi := y322Orthogonal3A5_checked i
  have hj := y322Orthogonal3A5_checked j
  simp only [y322Orthogonal3A5CheckAt, dite_eq_left i.isLt] at hi
  simp only [y322Orthogonal3A5CheckAt, dite_eq_left j.isLt] at hj
  rw [hi.2.2, hj.2.2] at h
  exact h

/-- The actual source A5 characteristic-three image has at least 720 elements. -/
theorem y322Orthogonal3A5Image_card_ge : 720 ≤ Nat.card y322Orthogonal3A5Image := by
  simpa only [Nat.card_fin] using
    Nat.card_le_card_of_injective _ y322Orthogonal3A5ImageCandidate_injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
