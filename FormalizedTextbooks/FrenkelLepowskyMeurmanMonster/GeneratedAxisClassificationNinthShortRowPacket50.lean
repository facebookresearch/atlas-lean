/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block50 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase50_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3200 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet50_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨3200 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger50_lo m, targetInteger50_lo m, sourceBinary50_lo m,
    targetBinary50_lo m, image50_lo m, phase50_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase50_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3232 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet50_hi : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨3232 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger50_hi m, targetInteger50_hi m, sourceBinary50_hi m,
    targetBinary50_hi m, image50_hi m, phase50_hi m⟩

/-- Every original row in the block50 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_50 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨3200 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet50_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 3232 + (m.val - 32) = 3200 + m.val := by omega
    have he : (⟨3232 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨3200 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet50_hi
      (⟨m.val - 32, by omega⟩ : Fin 32)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
