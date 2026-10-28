/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal acyclic contextual derivation table from the independent C322 coset trace. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextData06

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The seven literal chunks of the independent contextual derivation table. -/
def y322TCContextRawChunks : Fin 7 → Fin 4096 → Y322RawContextCertificate :=
  ![y322TCContextRawChunk00, y322TCContextRawChunk01, y322TCContextRawChunk02,
    y322TCContextRawChunk03, y322TCContextRawChunk04, y322TCContextRawChunk05,
    y322TCContextRawChunk06]

/-- Every literal contextual source-equation derivation in chronological order. -/
def y322TCContextRaw (i : Fin 28530) : Y322RawContextCertificate :=
  y322TCContextRawChunks ⟨i.val / 4096, by omega⟩
    ⟨i.val % 4096, Nat.mod_lt _ (by decide)⟩

/-- Exact word, source and strictly-earlier reference bounds, separating only finite padding. -/
def y322TCContextAllowedAt (index : ℕ) : Prop :=
  if h : index < 28530 then (y322TCContextRaw ⟨index, h⟩).Allowed 48648 48713 index else True

/-- All literal finite bounds of each contextual derivation record are decidable. -/
instance y322TCContextAllowedAtDecidable (index : ℕ) :
    Decidable (y322TCContextAllowedAt index) := by
  unfold y322TCContextAllowedAt
  split <;> infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
