/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- An independent full-isometry order bound from seven actual coordinate orbit injections. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalStabilizers

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each chain step is bounded by the candidate count times its prior stabilizer order. -/
theorem y322Orthogonal3DiagonalChain_card_step (i : Fin 7) :
    Nat.card (y322Orthogonal3DiagonalChain (i.val + 1)) ≤
      y322Orthogonal3DiagonalCandidateCount i * Nat.card (y322Orthogonal3DiagonalChain i.val) := by
  have h := y322FiniteAction_card_le_of_orbit (y322Orthogonal3DiagonalUnit i)
    (y322Orthogonal3DiagonalChainOrbitCandidate i)
    (y322Orthogonal3DiagonalChainOrbitCandidate_injective i)
  have hc : Nat.card (Y322Orthogonal3DiagonalCandidate i) =
      y322Orthogonal3DiagonalCandidateCount i := by
    rw [Nat.card_eq_fintype_card, y322Orthogonal3DiagonalCandidate_card]
  rw [hc, y322Orthogonal3DiagonalChain_stabilizer_card] at h
  exact h

/-- The independent full diagonal isometry group has order at most 18341406720. -/
theorem y322Orthogonal3DiagonalGroup_card_le :
    Nat.card y322Orthogonal3DiagonalGroup ≤ 18341406720 := by
  have h0 := y322Orthogonal3DiagonalChain_card_step 0
  have h1 := y322Orthogonal3DiagonalChain_card_step 1
  have h2 := y322Orthogonal3DiagonalChain_card_step 2
  have h3 := y322Orthogonal3DiagonalChain_card_step 3
  have h4 := y322Orthogonal3DiagonalChain_card_step 4
  have h5 := y322Orthogonal3DiagonalChain_card_step 5
  have h6 := y322Orthogonal3DiagonalChain_card_step 6
  norm_num [y322Orthogonal3DiagonalCandidateCount,
    y322Orthogonal3DiagonalChain_zero, y322Orthogonal3DiagonalChain_seven]
    at h0 h1 h2 h3 h4 h5 h6
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
