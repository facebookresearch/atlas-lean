/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorLiteralData

/-! Exact original source and target octad projections for the complete bridge. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Exact original projection on the outside source octad2818. -/
def generatedFeasibleContainingZeroOutsideAnchorSourceProjectionQ : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.diagonal (fun i => if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode 10).val).testBit i.val then 1 else 0)

/-- Exact original projection on the containing target octad780. -/
def generatedFeasibleContainingZeroOutsideAnchorTargetProjectionQ : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.diagonal (fun i => if (golayEncodedMask (generatedFeasibleContainingZeroOutsideAnchorCode 6).val).testBit i.val then 1 else 0)

/-- Full actual pair constituents determine every intermediate forward matrix entry. -/
def generatedFeasibleContainingZeroOutsideAnchorForwardMatrixQ (i j : Fin 24) : ℚ :=
  if i = j then generatedFeasibleContainingZeroOutsideAnchorMatrix1Q i i else
    (generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 0 (generatedAxisGlobalFinitePairIndex i j) +
      generatedFeasibleContainingZeroOutsideAnchorPairLiteralQ 0 1 (generatedAxisGlobalFinitePairIndex i j)) / 2

/-- Eight packets of three rows cover every physical matrix coordinate. -/
def generatedFeasibleContainingZeroOutsideAnchorMatrixPacketIndex (k : Fin 8) (i : Fin 3) : Fin 24 :=
  ⟨3 * k.val + i.val, by omega⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
