/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthIntegerStages

/-! Complete exact tensor packets after the literal phase-preserving fifth root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A complete integer numerator together with its actual physical tensor denominator. -/
abbrev GeneratedAxisGlobalIntegerTensorData := (Fin 4096 → Fin 24 → ℤ) × ℕ

/-- The exact successive integer packets of the chronological original local word. -/
def generatedAxisGlobalFifthIntegerChain (k : Fin 14)
    (u : GeneratedAxisGlobalIntegerTensorData) : ℕ → GeneratedAxisGlobalIntegerTensorData
  | 0 => u
  | n + 1 =>
      let v := generatedAxisGlobalFifthIntegerChain k u n
      let j : Fin 7 := ⟨n % 7, Nat.mod_lt _ (by decide)⟩
      (generatedAxisGlobalFifthIntegerStage k j v.1,
        generatedAxisGlobalFifthIntegerStageDenominator k j v.2)

/-- Every complete packet is exactly the actual local action of the identical chronological word. -/
theorem generatedAxisGlobalFifthIntegerChain_packet (k : Fin 14)
    (u : GeneratedAxisGlobalIntegerTensorData) (n : ℕ) :
    localTensorRepresentation
      (generatedAxisGlobalWordChain (fun j => generatedAxisGlobalFifthShortNormalizationFiber k
        ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n)
      (generatedAxisGlobalTensorIntegerPacket u.1 u.2) =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerChain k u n).1
          (generatedAxisGlobalFifthIntegerChain k u n).2 := by
  induction n with
  | zero =>
    simp only [generatedAxisGlobalWordChain, generatedAxisGlobalFifthIntegerChain, map_one,
      LinearEquiv.coe_one, id_eq]
  | succ n ih =>
    rw [generatedAxisGlobalWordChain, map_mul, LinearEquiv.mul_apply, ih]
    exact generatedAxisGlobalFifthIntegerStage_packet k _ _ _

/-- The full actual tensor output of one genuine fifth-axis root normalizing word. -/
def generatedAxisGlobalFifthIntegerRootData (k : Fin 14) :
    GeneratedAxisGlobalIntegerTensorData :=
  generatedAxisGlobalFifthIntegerChain k (generatedAxisGlobalFifthTensorInteger, 1) 7

/-- The displayed complete integer root packet is the actual fiber tensor output. -/
theorem generatedAxisGlobalFifthIntegerRoot_packet (k : Fin 14) :
    localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData k).1
          (generatedAxisGlobalFifthIntegerRootData k).2 := by
  rw [generatedAxisGlobalFifthTensorInteger_packet]
  exact generatedAxisGlobalFifthIntegerChain_packet k (generatedAxisGlobalFifthTensorInteger, 1) 7

/-- The same complete integer packet is the tensor part of the original actual Griess word. -/
theorem generatedAxisGlobalFifthIntegerRoot_actual (k : Fin 14) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis)).2.2 =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalFifthIntegerRootData k).1
          (generatedAxisGlobalFifthIntegerRootData k).2 := by
  rw [generatedAxisGlobalFifthShortWordFiber_encode, localConwayRawRepresentation_tensor]
  exact generatedAxisGlobalFifthIntegerRoot_packet k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
