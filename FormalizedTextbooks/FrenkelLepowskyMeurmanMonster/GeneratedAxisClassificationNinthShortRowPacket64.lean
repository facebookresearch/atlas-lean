/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCompactPhase

/-! Source block64 checks40 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceInteger64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetInteger64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem sourceBinary64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem targetBinary64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem image64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all32 actual source addresses.
private theorem phase64_lo : ∀ m : Fin 32,
    let k : Fin 4136 := ⟨4096 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet64_lo : ∀ m : Fin 32,
    GeneratedNinthShortRowCertificate (⟨4096 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger64_lo m, targetInteger64_lo m, sourceBinary64_lo m,
    targetBinary64_lo m, image64_lo m, phase64_lo m⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem sourceInteger64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem targetInteger64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem sourceBinary64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem targetBinary64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem image64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all8 actual source addresses.
private theorem phase64_hi : ∀ m : Fin 8,
    let k : Fin 4136 := ⟨4128 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  simp_rw [generatedNinth_mask_preferred_compact_phase]
  decide +kernel

private theorem packet64_hi : ∀ m : Fin 8,
    GeneratedNinthShortRowCertificate (⟨4128 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger64_hi m, targetInteger64_hi m, sourceBinary64_hi m,
    targetBinary64_hi m, image64_hi m, phase64_hi m⟩

/-- Every original row in the block64 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_64 : ∀ m : Fin 40,
    GeneratedNinthShortRowCertificate (⟨4096 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  by_cases hm : m.val < 32
  · exact packet64_lo (⟨m.val, hm⟩ : Fin 32)
  · have heval : 4128 + (m.val - 32) = 4096 + m.val := by omega
    have he : (⟨4128 + (m.val - 32), by omega⟩ : Fin 4136) =
        (⟨4096 + m.val, by omega⟩ : Fin 4136) := Fin.ext heval
    simpa only [he, heval] using packet64_hi
      (⟨m.val - 32, by omega⟩ : Fin 8)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
