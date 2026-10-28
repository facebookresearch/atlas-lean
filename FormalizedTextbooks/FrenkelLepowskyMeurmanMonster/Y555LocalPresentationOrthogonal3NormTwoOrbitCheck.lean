/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source-word recurrences in the independent norm orbit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormTwoOrbitData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Check the actual original source-word recurrence and exact norm of a bounded column. -/
def y322Orthogonal3NormTwoCheckAt (index : ℕ) : Prop :=
  if h : index < 702 then
    let i : Fin 702 := ⟨index, h⟩
    y322InverseWordOrbitChecked y322Orthogonal3NormTwoWord
      y322Orthogonal3NormTwoParent y322Orthogonal3NormTwoGenerator
      y322Orthogonal3NormTwoPoint y322Orthogonal3NormTwoVector i ∧
      y322Orthogonal3VectorNorm (y322Orthogonal3NormTwoVector i) = 2
  else True

/-- The exact bounded source-word recurrence and finite norm check is decidable. -/
instance y322Orthogonal3NormTwoCheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3NormTwoCheckAt index) := by
  unfold y322Orthogonal3NormTwoCheckAt
  split
  · dsimp only
    infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
