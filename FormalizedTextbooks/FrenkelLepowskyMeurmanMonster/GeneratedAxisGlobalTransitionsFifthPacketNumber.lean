/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthPacketQFinite

/-! Explicit integer numbering of every entry of the genuine fifth short packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Pair entries come first, followed by all sixty-four rows of each actual octad. -/
def generatedAxisGlobalFifthPacketNumber : GeneratedAxisGlobalFifthShortPacketIndex → Fin 4136
  | Sum.inl (s, p) => ⟨276 * s.val + p.val, by omega⟩
  | Sum.inr (j, e) => ⟨552 + 64 * j.val + e.val, by omega⟩

/-- The inverse numbering uses precisely the original pair and octad packet indices. -/
def generatedAxisGlobalFifthPacketFromNumber (i : Fin 4136) :
    GeneratedAxisGlobalFifthShortPacketIndex :=
  if h : i.val < 552 then
    Sum.inl (⟨i.val / 276, by omega⟩, ⟨i.val % 276, Nat.mod_lt _ (by omega)⟩)
  else
    Sum.inr (⟨(i.val - 552) / 64, by omega⟩,
      ⟨(i.val - 552) % 64, Nat.mod_lt _ (by omega)⟩)

/-- Numbering and decoding retain every actual packet entry. -/
theorem generatedAxisGlobalFifthPacketFromNumber_number
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthPacketFromNumber (generatedAxisGlobalFifthPacketNumber i) = i := by
  rcases i with ⟨s, p⟩ | ⟨j, e⟩
  · unfold generatedAxisGlobalFifthPacketFromNumber
    split_ifs with h
    · apply congrArg Sum.inl
      apply Prod.ext <;> apply Fin.ext <;>
        simp only [generatedAxisGlobalFifthPacketNumber] <;> omega
    · change ¬276 * s.val + p.val < 552 at h
      omega
  · unfold generatedAxisGlobalFifthPacketFromNumber
    split_ifs with h
    · change 552 + 64 * j.val + e.val < 552 at h
      omega
    · apply congrArg Sum.inr
      apply Prod.ext <;> apply Fin.ext <;>
        simp only [generatedAxisGlobalFifthPacketNumber] <;> omega

/-- Decoding a valid number returns that same number. -/
theorem generatedAxisGlobalFifthPacketNumber_fromNumber (i : Fin 4136) :
    generatedAxisGlobalFifthPacketNumber (generatedAxisGlobalFifthPacketFromNumber i) = i := by
  unfold generatedAxisGlobalFifthPacketFromNumber
  split <;> apply Fin.ext <;> simp only [generatedAxisGlobalFifthPacketNumber] <;> omega

/-- Seventeen batches cover all packet entries; their final redundant rows wrap safely. -/
def generatedAxisGlobalFifthPacketBatchNumber (b : Fin 17) (i : Fin 256) : Fin 4136 :=
  ⟨(256 * b.val + i.val) % 4136, Nat.mod_lt _ (by omega)⟩

/-- Each original packet entry occurs at its quotient and remainder batch coordinates. -/
theorem generatedAxisGlobalFifthPacketBatchNumber_cover (i : Fin 4136) :
    generatedAxisGlobalFifthPacketBatchNumber
      ⟨i.val / 256, by omega⟩ ⟨i.val % 256, Nat.mod_lt _ (by omega)⟩ = i := by
  apply Fin.ext
  simp only [generatedAxisGlobalFifthPacketBatchNumber]
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
