/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block44 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase44_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2816 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet44_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨2816 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger44_lo m, targetInteger44_lo m, sourceBinary44_lo m,
    targetBinary44_lo m, image44_lo m, phase44_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase44_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨2848 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet44_hi : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨2848 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger44_hi m, targetInteger44_hi m, sourceBinary44_hi m,
    targetBinary44_hi m, image44_hi m, phase44_hi m⟩

/-- Every original row in the block44 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_44 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨2816 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet44_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 2848 + (m.val - 32) = 2816 + m.val := by omega
    have he : (⟨2848 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨2816 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet44_hi
      (⟨m.val - 32, by omega⟩ : Fin 32)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
