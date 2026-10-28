/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block24 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase24_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1536 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet24_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨1536 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger24_lo m, targetInteger24_lo m, sourceBinary24_lo m,
    targetBinary24_lo m, image24_lo m, phase24_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase24_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1568 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet24_hi : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨1568 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger24_hi m, targetInteger24_hi m, sourceBinary24_hi m,
    targetBinary24_hi m, image24_hi m, phase24_hi m⟩

/-- Every original row in the block24 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_24 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨1536 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet24_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 1568 + (m.val - 32) = 1536 + m.val := by omega
    have he : (⟨1568 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨1536 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet24_hi
      (⟨m.val - 32, by omega⟩ : Fin 32)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
