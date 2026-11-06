/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedSourceBasics
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedSyndrome
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedOddSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketLabels

/-! Every packed packet mask is its genuine full preferred-Q element, including omega and theta. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The packed physical negative positions are the actual occurring octad's original positions. -/
theorem generatedSeventhXiShortPackedNegativeMask_actual (g : Fin 231) (e : Fin 64) :
    generatedSeventhXiShortPackedNegativeMask g e = generatedSeventhXiOctadNegativeMask g e := by
  simp only [generatedSeventhXiShortPackedNegativeMask, generatedSeventhXiOctadNegativeMask,
    generatedSeventhXiShortPackedOctadCoordinate_actual]

/-- Every packed octad mask retains the complete original preferred-Q source element. -/
theorem generatedSeventhXiShortPackedOctadMask_actual (g : Fin 231) (e : Fin 64) :
    griessShortQ (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily g, e))) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortPackedOctadMask g e) := by
  rw [generatedSeventhXiOctadPreferredMask_actual]
  congr 1
  rw [generatedSeventhXiShortPackedOctadMask,
    generatedSeventhXiShortPackedOctadTheta_actual,
    generatedSeventhXiShortPackedOctadCode_actual,
    generatedSeventhXiShortPackedOctadSyndrome_actual,
    generatedSeventhXiShortPackedNegativeMask_actual]
  unfold generatedSeventhXiOctadPreferredMask generatedSeventhXiShortModulationMask
    generatedSeventhXiShortTranslationMask generatedSeventhXiShortQJoinMask monsterNortonBitXor
  rw [← generatedSeventhXiShortPackedOmega_actual]
  have hm := Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
    (generatedSeventhXiShortThetaSplit (generatedSeventhXiOctadCode g)).isLt
    (generatedSeventhXiShortSyndromeMask (generatedSeventhXiOctadNegativeMask g e)).isLt)
  have hu := Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
    (generatedSeventhXiOctadCode g).isLt (show 2048 < 2 ^ 12 by decide))
  cases h : generatedSeventhXiShortPackedOmega e <;>
    simp [golayBooleanCast, hm, hu,
      Nat.mod_eq_of_lt (generatedSeventhXiOctadCode g).isLt]

/-- The packed odd omega correction retains both source weight parity and the distinguished bit. -/
theorem generatedSeventhXiShortPackedOddOmega_actual (g : Fin 512) (j : Fin 24) :
    golayBooleanCast (Bool.xor
      (generatedSeventhXiShortPackedOddWeightBits.testBit g.val)
      ((generatedSeventhXiShortPackedOddMask g).testBit j.val)) =
        griessOddOmegaCoefficient (generatedSeventhXiShortPackedOddCode g) j := by
  rw [golayBooleanCast_xor, (generatedSeventhXiShortPackedOdd_data g).2.2,
    (generatedSeventhXiShortPackedOdd_data g).2.1, generatedSeventhXiTensorPacked_mask]
  unfold griessOddOmegaCoefficient
  cases h : (golayEncodedMask (generatedSeventhXiShortPackedOddCode g).val).testBit j.val <;>
    simp [golayBooleanCast]

/-- Every packed odd mask retains the complete original preferred-Q source element. -/
theorem generatedSeventhXiShortPackedOddMask_actual (g : Fin 512) (j : Fin 24) :
    griessShortQ (Sum.inr (Sum.inr (generatedSeventhXiShortPackedOddCode g, j))) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortPackedOddPreferredMask g j) := by
  rw [generatedSeventhXiShortOddMask_actual]
  congr 1
  rw [generatedSeventhXiShortPackedOddPreferredMask,
    (generatedSeventhXiShortPackedOdd_data g).1]
  unfold generatedSeventhXiShortTranslationMask generatedSeventhXiShortQJoinMask
    monsterNortonBitXor
  rw [← generatedSeventhXiShortPackedOddOmega_actual]
  have hd : (generatedSeventhXiShortPackedOddCode g).val < 4096 := by
    exact lt_trans (generatedSeventhXiShortPackedOddCode g).isLt (by decide)
  have hm := Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
    (generatedSeventhXiShortThetaSplit ⟨(generatedSeventhXiShortPackedOddCode g).val, hd⟩).isLt
    (generatedSeventhXiShortCocodeColumn j).isLt)
  have hu := Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 12)
    hd (show 2048 < 2 ^ 12 by decide))
  cases h : Bool.xor (generatedSeventhXiShortPackedOddWeightBits.testBit g.val)
      ((generatedSeventhXiShortPackedOddMask g).testBit j.val) <;>
    simp [golayBooleanCast, hm, hu, Nat.mod_eq_of_lt hd]

/-- Every position of the complete short packet has its actual preferred-Q mask. -/
theorem generatedSeventhXiShortPacketMask_actual (k : Fin 27624) :
    griessShortQ (generatedSeventhXiShortPacketLabel k) =
      generatedSeventhXiShortQMask (generatedSeventhXiShortPacketMask k) :=
  generatedSeventhXiShortPacketLabel_mask generatedSeventhXiShortPackedOctadMask_actual
    generatedSeventhXiShortPackedOddMask_actual k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
