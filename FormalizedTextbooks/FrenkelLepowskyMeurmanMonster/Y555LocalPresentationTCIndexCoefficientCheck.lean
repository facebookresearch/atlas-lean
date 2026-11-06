/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source-letter restrictions on all proposed local table-edge coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdges

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Check that every literal edge coefficient uses only actual E7 source and prefix letters. -/
def y322TCIndexCoefficientAllowedAt (index : ℕ) : Prop :=
  if h : index < 25272 then
    y322TCIndexE7WordAllowed
      (y322TCIndexEdgeAt ⟨index / 8, by omega⟩
        ⟨index % 8, Nat.mod_lt _ (by decide)⟩).coefficient
  else True

/-- Every exact proposed edge coefficient restriction is decidable. -/
instance y322TCIndexCoefficientAllowedAtDecidable (index : ℕ) :
    Decidable (y322TCIndexCoefficientAllowedAt index) := by
  unfold y322TCIndexCoefficientAllowedAt
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
