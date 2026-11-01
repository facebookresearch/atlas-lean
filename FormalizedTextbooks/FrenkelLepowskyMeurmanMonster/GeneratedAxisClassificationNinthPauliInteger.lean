/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinEncoding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors

/-! Exact packed translations and modulations retain the actual central Q coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual positive Q lift with the specified translation and modulation masks. -/
def generatedNinthPauliQ (a b : Fin 4096) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients a) (golayLabelCoefficients b)), 1⟩

/-- The positive Q lift translates by its original twelve-bit address. -/
theorem generatedNinth_pauli_translation (a b : Fin 4096) :
    spinTranslation (generatedNinthPauliQ a b) = golayLabelCoefficients a := by
  ext i
  simp [spinTranslation, generatedNinthPauliQ]

/-- The positive Q lift modulates by its original twelve-bit mask. -/
theorem generatedNinth_pauli_modulation (a b : Fin 4096) :
    spinModulation (generatedNinthPauliQ a b) = golayLabelCoefficients b := by
  ext i
  change Fin.append (golayLabelCoefficients a) (golayLabelCoefficients b)
    (Fin.natAdd 12 i) = golayLabelCoefficients b i
  exact Fin.append_right _ _ i

/-- The compact parity sign and XOR address of this actual positive Q operator. -/
def generatedNinthPauliInteger (a b : Fin 4096) (v : NortonUIntegerVector) :
    NortonUIntegerVector := fun n =>
  (if (monsterCo1GeometryBinaryMaskDot 12 b.val n.val).testBit 0 then -1 else 1) *
    v (generatedSixthSpinLabelXor n a)

/-- Packed parity retains the complete sign of the actual positive Q lift. -/
theorem generatedNinth_pauli_integer (a b : Fin 4096) (v : NortonUIntegerVector) :
    nortonUIntegerQ (generatedNinthPauliQ a b) v = generatedNinthPauliInteger a b v := by
  ext n
  change nortonUIntegerSign (spinPhase (generatedNinthPauliQ a b)
    (golayLabelCoefficients n)) *
    v (nortonUIntegerLabel (golayLabelCoefficients n +
      spinTranslation (generatedNinthPauliQ a b))) = _
  have hc : toAdd (generatedNinthPauliQ a b).coeff = (0 : ZMod 2) := rfl
  rw [spinPhase, hc, zero_add]
  rw [generatedNinth_pauli_modulation, generatedNinth_pauli_translation,
    ← generatedSixth_spin_label_xor, nortonUIntegerLabel_coeff]
  change nortonUIntegerSign (spinDot (golayLabelCoefficients b) (golayLabelCoefficients n)) * _ = _
  have hd := monsterCo1GeometryBinaryMaskDot_decode 12 b.val n.val
  change (if (monsterCo1GeometryBinaryMaskDot 12 b.val n.val).testBit 0 then
    (1 : ZMod 2) else 0) = spinDot (golayLabelCoefficients b) (golayLabelCoefficients n) at hd
  rw [← hd]
  cases h : (monsterCo1GeometryBinaryMaskDot 12 b.val n.val).testBit 0 <;>
    simp [generatedNinthPauliInteger, nortonUIntegerSign, h]

/-- The compact integer operator embeds as the literal actual Q spin action. -/
theorem generatedNinth_pauli_integer_embed (a b : Fin 4096) (v : NortonUIntegerVector) :
    spinRepresentation (generatedNinthPauliQ a b) (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (generatedNinthPauliInteger a b v) := by
  rw [nortonUIntegerQ_embed, generatedNinth_pauli_integer]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
