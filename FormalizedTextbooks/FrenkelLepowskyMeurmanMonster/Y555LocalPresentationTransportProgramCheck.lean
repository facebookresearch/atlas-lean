/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Decidable exact reference bounds for the literal chronological transporter instructions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgramData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal chronological reference-bound predicate is decidable. -/
instance y322TransportAllowedAtDecidable (index : ℕ) :
    Decidable (y322TransportAllowedAt index) := by
  unfold y322TransportAllowedAt
  split <;> infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
