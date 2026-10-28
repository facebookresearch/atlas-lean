/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block26 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase26_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1664 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet26_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨1664 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger26_lo m, targetInteger26_lo m, sourceBinary26_lo m,
    targetBinary26_lo m, image26_lo m, phase26_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase26_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨1696 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet26_hi : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨1696 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger26_hi m, targetInteger26_hi m, sourceBinary26_hi m,
    targetBinary26_hi m, image26_hi m, phase26_hi m⟩

/-- Every original row in the block26 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_26 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨1664 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet26_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 1696 + (m.val - 32) = 1664 + m.val := by omega
    have he : (⟨1696 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨1664 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet26_hi
      (⟨m.val - 32, by omega⟩ : Fin 32)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
