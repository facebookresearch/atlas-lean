/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates

/-! Source block10 checks64 chronological rows against all six original arithmetic
obligations: integer source and target, intrinsic masks, actual image and full phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem sourceInteger10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    generatedNinthShortRowSourceIntegral (generatedNinthShortRowSource k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowSourceCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem targetInteger10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthShortRowTarget k) =
      leechBasisMatrix *ᵥ generatedNinthShortRowTargetCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem sourceBinary10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowSourceCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowSourceMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem targetBinary10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthShortRowTargetCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthShortRowTargetMask k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem image10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    sixthFrameOrbitMaskApply generatedNinthQBinaryColumns (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowTargetMask k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check this original arithmetic obligation at all64 actual source addresses.
private theorem phase10 : ∀ m : Fin 64,
    let k : Fin 4136 := ⟨640 + m.val, by omega⟩
    generatedNinthMaskPreferredPhase (generatedNinthShortRowSourceMask k) =
      generatedNinthShortRowPhase k := by
  decide +kernel

/-- Every original row in the block10 has a complete genuine-source certificate. -/
theorem generatedNinth_short_row_packet_10 : ∀ m : Fin 64,
    GeneratedNinthShortRowCertificate (⟨640 + m.val, by omega⟩ : Fin 4136) := by
  intro m
  exact ⟨sourceInteger10 m, targetInteger10 m, sourceBinary10 m, targetBinary10 m,
    image10 m, phase10 m⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
