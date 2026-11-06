/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingCoordinatesData

/-! Exact genuine integer and intrinsic binary coordinates on sixteen original marking labels.
Actual coefficient classification is a separate proof. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Verify only the sixteen displayed marking labels against the actual coordinate matrices.
/-- Exact original marking integer coordinates on chronological block00. -/
theorem generatedNinth_marking_integer_packet_00 : ∀ n : Fin 16,
    let k : Fin 144 := ⟨0 + n.val, by omega⟩
    generatedNinthShortRowTargetIntegral (generatedNinthMarkingLabel k) =
      leechBasisMatrix *ᵥ generatedNinthMarkingCoordinates k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Verify only the sixteen displayed marking labels against the actual coordinate matrices.
/-- Exact original marking binary coordinates on chronological block00. -/
theorem generatedNinth_marking_binary_packet_00 : ∀ n : Fin 16,
    let k : Fin 144 := ⟨0 + n.val, by omega⟩
    leechHyperbolicInverse *ᵥ integerParity (generatedNinthMarkingCoordinates k) =
      monsterCo1GeometryBinaryMaskDecode (generatedNinthMarkingMask k) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
