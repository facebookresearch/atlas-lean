/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

/-! Source block4 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem sourceInteger04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem targetInteger04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem sourceBinary04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem targetBinary04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem image04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem phase04 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨256 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  decide +kernel

/-- Every original row in the block4 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_04 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨256 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger04 m, targetInteger04 m, sourceBinary04 m, targetBinary04 m,
    image04 m, phase04 m⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
