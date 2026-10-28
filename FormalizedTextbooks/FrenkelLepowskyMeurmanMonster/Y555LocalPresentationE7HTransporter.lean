/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Triviality of the actual chronological E7 transporter word in the source C322 quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HNodeNormalization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7HNodeEmbedding

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The final ancestor normalization produces exactly the empty positive source word. -/
theorem y322E7HNodeWord_last : y322E7HNodeWord 4412 = [] := by
  decide +kernel

/-- Chronological transporter H38539 is one in the actual original C322 presentation. -/
theorem y322TransportH38539_value : y322LocalProgramValue y322TransportProgram 38539 = 1 := by
  rw [← y322E7HNodeEmbedding_last, y322E7HNodeTransport_value, y322E7HNodeProgram_value,
    y322E7HNodeWord_last]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
