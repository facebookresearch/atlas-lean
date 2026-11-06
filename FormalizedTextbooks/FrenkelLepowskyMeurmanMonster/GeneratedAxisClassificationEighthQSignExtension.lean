/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthFlagData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode

/-! Even patterns on the original twelve-coordinate dodecad extend to actual Golay code. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The twelve genuine coordinates of the original dodecad, in increasing order. -/
def generatedEighthDodecadCoordinates : Fin 12 → Fin 24 :=
  ![0, 1, 2, 3, 5, 6, 9, 10, 16, 18, 22, 23]

/-- Original encoder words prescribing each of the first eleven bits and the last parity bit. -/
def generatedEighthDodecadSignInverseMask : Fin 11 → Fin 4096 :=
  ![3133, 1522, 1548, 1985, 179, 190, 32, 35, 203, 205, 254]

set_option maxHeartbeats 2000000 in
-- Check all 132 original encoded bits; the final bit is the sum of the first eleven.
/-- Each literal original codeword has precisely the displayed two-bit dodecad restriction. -/
theorem generatedEighth_dodecad_sign_inverse_certificate : ∀ j : Fin 11, ∀ i : Fin 12,
    (sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)).val
      (generatedEighthDodecadCoordinates i) =
        if i = j.castSucc ∨ i = Fin.last 11 then 1 else 0 := by
  decide +kernel

/-- Each original inverse word fixes the distinguished outside coordinate twenty. -/
theorem generatedEighth_dodecad_sign_inverse_twenty : ∀ j : Fin 11,
    (sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)).val 20 = 0 := by
  decide +kernel

/-- The genuine codeword extending the first eleven prescribed dodecad signs. -/
def generatedEighthDodecadSignExtensionCode (bits : Fin 12 → ZMod 2) : golayCode :=
  ∑ j : Fin 11, bits j.castSucc •
    sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)

/-- The genuine extended codeword fixes the distinguished outside coordinate twenty. -/
theorem generatedEighth_dodecad_sign_extension_twenty (bits : Fin 12 → ZMod 2) :
    (generatedEighthDodecadSignExtensionCode bits).val 20 = 0 := by
  change (∑ j : Fin 11, bits j.castSucc •
    (sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)).val) 20 = 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    generatedEighth_dodecad_sign_inverse_twenty, mul_zero, Finset.sum_const_zero]

/-- All first eleven actual dodecad coordinates have their prescribed original signs. -/
theorem generatedEighth_dodecad_sign_extension_first (bits : Fin 12 → ZMod 2) (i : Fin 11) :
    (generatedEighthDodecadSignExtensionCode bits).val
      (generatedEighthDodecadCoordinates i.castSucc) = bits i.castSucc := by
  change (∑ j : Fin 11, bits j.castSucc •
    (sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)).val)
      (generatedEighthDodecadCoordinates i.castSucc) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    generatedEighth_dodecad_sign_inverse_certificate]
  have hne : i.castSucc ≠ (11 : Fin 12) := Fin.castSucc_ne_last i
  simp [hne]

/-- The last actual dodecad coordinate is the parity of the first eleven prescribed signs. -/
theorem generatedEighth_dodecad_sign_extension_last (bits : Fin 12 → ZMod 2) :
    (generatedEighthDodecadSignExtensionCode bits).val
      (generatedEighthDodecadCoordinates (Fin.last 11)) = ∑ j : Fin 11, bits j.castSucc := by
  change (∑ j : Fin 11, bits j.castSucc •
    (sourceGeneratedSignCode (generatedEighthDodecadSignInverseMask j)).val)
      (generatedEighthDodecadCoordinates (Fin.last 11)) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    generatedEighth_dodecad_sign_inverse_certificate, or_true, ite_true, mul_one]

/-- Every actual even twelve-bit sign pattern extends to a genuine encoded Golay codeword. -/
theorem generatedEighth_dodecad_even_sign_extension (bits : Fin 12 → ZMod 2)
    (heven : ∑ i, bits i = 0) :
    ∀ i, (generatedEighthDodecadSignExtensionCode bits).val
      (generatedEighthDodecadCoordinates i) = bits i := by
  apply Fin.lastCases
  · rw [generatedEighth_dodecad_sign_extension_last]
    rw [Fin.sum_univ_castSucc] at heven
    calc
      (∑ j : Fin 11, bits j.castSucc) = (∑ j : Fin 11, bits j.castSucc) + 0 := by rw [add_zero]
      _ = (∑ j : Fin 11, bits j.castSucc) +
          ((∑ j : Fin 11, bits j.castSucc) + bits (Fin.last 11)) := by rw [heven]
      _ = bits (Fin.last 11) := by rw [← add_assoc, ZModModule.add_self, zero_add]
  · exact generatedEighth_dodecad_sign_extension_first bits

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
