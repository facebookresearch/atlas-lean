/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite fingerprints and sorted-label certificates for source root transports. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCMembershipEval
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact matrix fingerprint, sorted position, inverse position and adjacent-order checks. -/
def y322Orthogonal3TCMembershipCheckAt (index : ℕ) : Prop :=
  if h : index < 3159 then
    let i : Fin 3159 := ⟨index, h⟩
    y322Orthogonal3TCMembershipEval
        (y322Orthogonal3TCCacheMatrix (y322Orthogonal3TCRepresentativeCache i)) =
      y322Orthogonal3TCMembershipValue i ∧
    y322Orthogonal3TCMembershipValue i =
      y322Orthogonal3TCMembershipSorted (y322Orthogonal3TCMembershipSortPosition i) ∧
    y322Orthogonal3TCMembershipInverseSortPosition (y322Orthogonal3TCMembershipSortPosition i) = i ∧
    if hn : index + 1 < 3159 then
      y322Orthogonal3TCMembershipSorted i <
        y322Orthogonal3TCMembershipSorted ⟨index + 1, hn⟩
    else True
  else True

/-- Each exact finite root-transport fingerprint and sorted-label check is decidable. -/
instance y322Orthogonal3TCMembershipCheckAtDecidable (index : ℕ) :
    Decidable (y322Orthogonal3TCMembershipCheckAt index) := by
  unfold y322Orthogonal3TCMembershipCheckAt
  split
  · dsimp only
    infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
