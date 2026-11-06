/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputTheta

/-! A compact checked encoding of every original fifth-packet input. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original physical negative mask using the checked fifty-six input octad frames. -/
def generatedAxisGlobalFifthInputNegativeMask (j : Fin 56) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun (k : Fin 8) (m : ℕ) =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFifthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- The compact negative mask is exactly the original physical parity vector. -/
theorem generatedAxisGlobalFifthInputNegativeMask_decode (j : Fin 56) (e : Fin 64) :
    monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedAxisGlobalFifthInputNegativeMask j e) =
        integerParity (generatedAxisGlobalFifthShortNegativeInteger j e) := by
  funext i
  unfold monsterCo1GeometryBinaryMaskDecode generatedAxisGlobalFifthInputNegativeMask
    integerParity generatedAxisGlobalFifthShortNegativeInteger
  split <;> simp_all

/-- Every original input mask includes its code, cocode, and preferred Ω correction. -/
def generatedAxisGlobalFifthInputCompact : GeneratedAxisGlobalFifthShortPacketIndex → ℕ
  | Sum.inl p => generatedAxisGlobalShortMask (Sum.inl p)
  | Sum.inr (j, e) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedFifthEvenRootCode j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (parkerThetaMask (generatedFifthEvenRootCode j).val)
        (generatedAxisGlobalCocodeMask (generatedAxisGlobalFifthInputNegativeMask j e)))

/-- Each compact input is the entire original preferred-Q element, with its actual central bit. -/
theorem generatedAxisGlobalFifthInputCompact_Q_actual
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthPacketQFinite i =
      generatedAxisGlobalQMask (generatedAxisGlobalFifthInputCompact i) := by
  rcases i with p | ⟨j, e⟩
  · exact generatedAxisGlobalShortMask_Q_actual (Sum.inl p)
  · apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      symm
      change monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthInputCompact _) = _
      simp only [generatedAxisGlobalFifthInputCompact, generatedAxisGlobalSourceMaskJoin_decode,
        monsterCo1GeometryBinaryMaskDecode_xor, generatedAxisGlobalOmegaMask_decode,
        generatedAxisGlobalCocodeMask_decode, generatedAxisGlobalFifthInputNegativeMask_decode]
      rfl
    · rfl

/-- The same original input formula with the checked fifty-six theta lookups shared. -/
def generatedAxisGlobalFifthInputCompactCached : GeneratedAxisGlobalFifthShortPacketIndex → ℕ
  | Sum.inl p => generatedAxisGlobalShortMask (Sum.inl p)
  | Sum.inr (j, e) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedFifthEvenRootCode j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (generatedAxisGlobalFifthInputThetaData j)
        (generatedAxisGlobalCocodeMask (generatedAxisGlobalFifthInputNegativeMask j e)))

/-- Sharing the actual theta values changes no original input coordinate or central section. -/
theorem generatedAxisGlobalFifthInputCompact_eq_cached
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedAxisGlobalFifthInputCompact i = generatedAxisGlobalFifthInputCompactCached i := by
  rcases i with p | ⟨j, e⟩
  · rfl
  · simp only [generatedAxisGlobalFifthInputCompact, generatedAxisGlobalFifthInputCompactCached,
      generatedAxisGlobalFifthInputThetaData_actual]

set_option maxHeartbeats 200000000 in
-- Check all4352 compact original words, including the final valid repeated entries.
set_option maxRecDepth 10000 in
/-- Every candidate input word equals its complete compact original coordinate formula. -/
theorem generatedAxisGlobalFifthInputCompact_checked (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthInputCompact (generatedAxisGlobalFifthPacketFromNumber
      (generatedAxisGlobalFifthPacketBatchNumber b i)) =
        generatedAxisGlobalFifthInputMaskData b i := by
  rw [generatedAxisGlobalFifthInputCompact_eq_cached]
  revert b i
  decide +kernel

/-- The checked input table is the full actual original lift on every wrapped batch entry. -/
theorem generatedAxisGlobalFifthInputCompact_data_Q_actual (b : Fin 17) (i : Fin 256) :
    generatedAxisGlobalFifthPacketQFinite (generatedAxisGlobalFifthPacketFromNumber
      (generatedAxisGlobalFifthPacketBatchNumber b i)) =
        generatedAxisGlobalQMask (generatedAxisGlobalFifthInputMaskData b i) := by
  rw [generatedAxisGlobalFifthInputCompact_Q_actual,
    generatedAxisGlobalFifthInputCompact_checked]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
