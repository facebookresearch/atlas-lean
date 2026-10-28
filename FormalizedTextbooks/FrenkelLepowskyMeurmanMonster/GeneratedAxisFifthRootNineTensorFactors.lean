/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot09Packet

/-! Eight complete original source factors through the actual seven-stage root-nine word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
-- The complete seven-stage original source word has a deep factor-expression spine.
set_option maxRecDepth 10000

/-- A full original spin numerator, physical numerator, and both actual denominators. -/
abbrev GeneratedFifthRootNineTensorFactorData :=
  (Fin 4096 → ℤ) × (Fin 24 → ℤ) × ℕ × ℕ

/-- Every original factor after each chronological stage of the genuine root-nine word. -/
def generatedFifthRootNineTensorFactorData (r : Fin 8) :
    ℕ → GeneratedFifthRootNineTensorFactorData
  | 0 => (generatedTwelfthTensorSourceSpin r, generatedTwelfthTensorSourceSpatial r, 1, 1)
  | n + 1 =>
      let v := generatedFifthRootNineTensorFactorData r n
      let j : Fin 7 := ⟨n % 7, Nat.mod_lt _ (by decide)⟩
      (generatedTwelfthTensorSourceStageSpin 9 j v.1,
        generatedTwelfthTensorSourceStageSpatial 9 j v.2.1,
        generatedTwelfthTensorSourceStageSpinDenominator 9 j v.2.2.1,
        generatedTwelfthTensorSourceStageSpatialDenominator 9 j v.2.2.2)

/-- Every original physical coordinate of one complete transported source factor. -/
def generatedFifthRootNineTensorFactor (r : Fin 8) (n : ℕ) : SpinIndex → Fin 24 → ℝ :=
  let v := generatedFifthRootNineTensorFactorData r n
  generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalOddTensorFactor v.1 v.2.1)
    (v.2.2.1 * v.2.2.2)

/-- The actual initial eight-factor source is the entire original Fifth tensor. -/
theorem generatedFifthRootNine_tensor_factor_initial :
    (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ r : Fin 8, generatedFifthRootNineTensorFactor r 0 := by
  exact generatedTwelfth_tensor_source_actual

/-- Each original normalization stage retains all spin phases and both true denominators. -/
theorem generatedFifthRootNine_tensor_factor_stage (r : Fin 8) (n : ℕ) :
    localTensorRepresentation
        (generatedAxisGlobalFifthShortNormalizationFiber 9
          ⟨n % 7, Nat.mod_lt _ (by decide)⟩)
        (generatedFifthRootNineTensorFactor r n) =
      generatedFifthRootNineTensorFactor r (n + 1) := by
  exact generatedTwelfth_tensor_source_stage_packet 9 _ _ _ _ _

/-- Every chronological word prefix takes each complete source factor to its actual packet. -/
theorem generatedFifthRootNine_tensor_factor_chain (r : Fin 8) (n : ℕ) :
    localTensorRepresentation
        (generatedAxisGlobalWordChain
          (fun j => generatedAxisGlobalFifthShortNormalizationFiber 9
            ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n)
        (generatedFifthRootNineTensorFactor r 0) =
      generatedFifthRootNineTensorFactor r n := by
  induction n with
  | zero => simp [generatedAxisGlobalWordChain]
  | succ n ih =>
      rw [generatedAxisGlobalWordChain, map_mul, LinearEquiv.mul_apply, ih]
      exact generatedFifthRootNine_tensor_factor_stage r n

/-- Each arbitrary word prefix transports the entire eight-factor original source tensor. -/
theorem generatedFifthRootNine_tensor_factors_chain (n : ℕ) :
    localTensorRepresentation
        (generatedAxisGlobalWordChain
          (fun j => generatedAxisGlobalFifthShortNormalizationFiber 9
            ⟨j % 7, Nat.mod_lt _ (by decide)⟩) n)
        (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ r : Fin 8, generatedFifthRootNineTensorFactor r n := by
  rw [generatedFifthRootNine_tensor_factor_initial, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact generatedFifthRootNine_tensor_factor_chain r n

/-- The full genuine seven-stage local word transports all eight original source factors. -/
theorem generatedFifthRootNine_tensor_factor_word :
    localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 9)
        (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ r : Fin 8, generatedFifthRootNineTensorFactor r 7 := by
  unfold generatedAxisGlobalFifthShortWordFiber
  rw [← generatedFifthRootNine_tensor_factors_chain 7]

/-- Every actual incoming root-nine tensor coordinate has the complete eight-factor formula. -/
theorem generatedFifthRootNine_incoming_tensor_factors :
    generatedAxisGlobalFifthRoot09Packet.2.2 =
      ∑ r : Fin 8, generatedFifthRootNineTensorFactor r 7 := by
  rw [← generatedAxisGlobalFifthRoot09Packet_actual,
    generatedAxisGlobalFifthShortWordFiber_encode, localConwayRawRepresentation_tensor]
  exact generatedFifthRootNine_tensor_factor_word

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
