/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source-word recurrences in the independent norm orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormOneOrbitData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Check the actual original source-word recurrence and exact norm of a bounded column. -/
def y322Orthogonal3NormOneCheckAt (index : ℕ) : Prop :=
  if h : index < 756 then
    let i : Fin 756 := ⟨index, h⟩
    y322InverseWordOrbitChecked y322Orthogonal3NormOneWord
      y322Orthogonal3NormOneParent y322Orthogonal3NormOneGenerator
      y322Orthogonal3NormOnePoint y322Orthogonal3NormOneVector i ∧
      y322Orthogonal3VectorNorm (y322Orthogonal3NormOneVector i) = 1
  else True

/-- The exact bounded source-word recurrence and finite norm check is decidable. -/
instance y322Orthogonal3NormOneCheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3NormOneCheckAt index) := by
  unfold y322Orthogonal3NormOneCheckAt
  split
  · dsimp only
    infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
