/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerPrimitives
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialInteger
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortFiber

/-! Exact integer semantics of every original stage in the actual fifth root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A complete integer tensor numerator after the literal permutation and sign stages. -/
def generatedAxisGlobalFifthIntegerSignedStage (k : Fin 14) (j : Fin 7)
    (N : Fin 4096 → Fin 24 → ℤ) : Fin 4096 → Fin 24 → ℤ :=
  generatedAxisGlobalSignIntegerAction
    (generatedAxisGlobalMonomialIntegerAction
      (generatedAxisGlobalFifthShortNormalizationWords k j) N)
    (generatedAxisGlobalFifthShortNormalizationSigns k j) 0

/-- The complete integer numerator after the actual optional Xi stage. -/
def generatedAxisGlobalFifthIntegerStage (k : Fin 14) (j : Fin 7)
    (N : Fin 4096 → Fin 24 → ℤ) : Fin 4096 → Fin 24 → ℤ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then
    generatedAxisGlobalXiIntegerAction (generatedAxisGlobalFifthIntegerSignedStage k j N)
  else generatedAxisGlobalFifthIntegerSignedStage k j N

/-- Exact denominator multiplication in the same literal source stage. -/
def generatedAxisGlobalFifthIntegerStageDenominator (k : Fin 14) (j : Fin 7) (D : ℕ) : ℕ :=
  if generatedAxisGlobalFifthShortNormalizationXi k j then 16 * (2 * D) else 2 * D

/-- Every complete integer stage is the actual real local-fiber action, retaining all phases. -/
theorem generatedAxisGlobalFifthIntegerStage_packet (k : Fin 14) (j : Fin 7)
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation (generatedAxisGlobalFifthShortNormalizationFiber k j)
      (generatedAxisGlobalTensorIntegerPacket N D) =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerStage k j N)
          (generatedAxisGlobalFifthIntegerStageDenominator k j D) := by
  rw [generatedAxisGlobalFifthShortNormalizationFiber, map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [generatedAxisGlobalMonomialInteger_packet, generatedAxisGlobalSignInteger_packet]
  change localTensorRepresentation
    (if generatedAxisGlobalFifthShortNormalizationXi k j then xiSpinLocalFiber else 1)
    (generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerSignedStage k j N)
      (2 * D)) = _
  cases hx : generatedAxisGlobalFifthShortNormalizationXi k j with
  | false =>
    simp only [hx, Bool.false_eq_true, ↓reduceIte, map_one, LinearEquiv.coe_one, id_eq,
      generatedAxisGlobalFifthIntegerStage, generatedAxisGlobalFifthIntegerStageDenominator]
  | true =>
    simp only [hx, ↓reduceIte, generatedAxisGlobalFifthIntegerStage,
      generatedAxisGlobalFifthIntegerStageDenominator]
    exact generatedAxisGlobalXiInteger_packet _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
