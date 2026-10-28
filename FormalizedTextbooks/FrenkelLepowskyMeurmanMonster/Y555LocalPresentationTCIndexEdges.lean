/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact full-table edge targets, coefficients and finite representative labels. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdgesData06

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The chronological literal edge-target chunks. -/
def y322TCIndexEdgesChunk : Fin 7 → Fin 4096 → Y322TCIndexEdge :=
  ![y322TCIndexEdgesChunk00, y322TCIndexEdgesChunk01, y322TCIndexEdgesChunk02,
    y322TCIndexEdgesChunk03, y322TCIndexEdgesChunk04, y322TCIndexEdgesChunk05,
    y322TCIndexEdgesChunk06]

/-- Each proposed source-generator edge names its actual equation and literal E7 coefficient. -/
def y322TCIndexEdgeAt (i : Fin 3159) (g : Fin 8) : Y322TCIndexEdge :=
  let index := i.val * 8 + g.val
  y322TCIndexEdgesChunk ⟨index / 4096, by omega⟩
    ⟨index % 4096, Nat.mod_lt _ (by decide)⟩

/-- Packed coefficient letters belong to original E7 generators or actual H prefix names. -/
def y322TCIndexE7WordAllowed (word : List ℕ) : Prop :=
  ∀ packed ∈ word, packed / 2 < 7 ∨ (8 ≤ packed / 2 ∧ packed / 2 < 38548)

/-- The exact packed E7 coefficient restriction is finite and decidable. -/
instance y322TCIndexE7WordAllowedDecidable (word : List ℕ) :
    Decidable (y322TCIndexE7WordAllowed word) := by
  unfold y322TCIndexE7WordAllowed
  infer_instance

/-- The exact finite alphabet bound follows from the more precise literal E7 restriction. -/
theorem y322TCIndexE7WordAllowed_alphabet (word : List ℕ)
    (h : y322TCIndexE7WordAllowed word) : y322RawEquationWordAllowed 48648 word := by
  intro packed hp
  obtain ha | ⟨ha, hb⟩ := h packed hp <;> omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
