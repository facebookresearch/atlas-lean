/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal E7 source-generator checks for the actual chronological transporter words. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationE7ParabolicWords

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original H word-program prefix uses only the seven declared E7 source generators. -/
def y322TransportE7AllowedAt (index : ℕ) : Prop :=
  if h : index < 38540 then
    (y322TransportRaw ⟨index, lt_trans h (by decide)⟩).E7Allowed
  else True

/-- The exact raw prefix source-generator check is decidable. -/
instance y322TransportE7AllowedAtDecidable (index : ℕ) :
    Decidable (y322TransportE7AllowedAt index) := by
  unfold y322TransportE7AllowedAt
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
