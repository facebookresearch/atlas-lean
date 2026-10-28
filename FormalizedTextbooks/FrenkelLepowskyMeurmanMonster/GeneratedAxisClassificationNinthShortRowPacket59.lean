/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block59 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase59_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3776 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet59_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨3776 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger59_lo m, targetInteger59_lo m, sourceBinary59_lo m,
    targetBinary59_lo m, image59_lo m, phase59_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase59_hi : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨3808 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet59_hi : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨3808 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger59_hi m, targetInteger59_hi m, sourceBinary59_hi m,
    targetBinary59_hi m, image59_hi m, phase59_hi m⟩

/-- Every original row in the block59 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_59 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨3776 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet59_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 3808 + (m.val - 32) = 3776 + m.val := by omega
    have he : (⟨3808 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨3776 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet59_hi
      (⟨m.val - 32, by omega⟩ : Fin 32)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
