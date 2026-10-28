/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSignPauliChoices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignCard

/-! The genuine adjusted Pauli translations have the prescribed original Conway sign classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Golay codeword encoded by the genuine adjusted Pauli translation. -/
def generatedSixthSignPauliCode (j : Fin 10) : golayCode :=
  golayEncoder.rangeRestrict (generatedSixthSignPauliTranslation j)

private theorem omega_code :
    golayEncoder.rangeRestrict (Pi.single (11 : Fin 12) 1) =
      monsterCo1GeometryAllOneCode := by
  apply Subtype.ext
  exact golay_all_one

private theorem all_one_class :
    (QuotientGroup.mk' signsSubgroup)
      (golaySignHom (Multiplicative.ofAdd monsterCo1GeometryAllOneCode)) = 1 := by
  rw [monsterCo1GeometryAllOne_negative]
  exact (QuotientGroup.eq_one_iff leechNegativeIdentity).mpr (Or.inr (fun _ => rfl))

/-- Adding Ω to any genuine code translation changes no actual Conway quotient sign. -/
theorem generatedSixth_sign_class_add_omega (a : SpinIndex) (b : ZMod 2) :
    (QuotientGroup.mk
      (golaySignIsometry (golayEncoder.rangeRestrict (a + b • Pi.single 11 1))) : Co1) =
    QuotientGroup.mk (golaySignIsometry (golayEncoder.rangeRestrict a)) := by
  have hb : b = 0 ∨ b = 1 := by revert b; decide +kernel
  rcases hb with rfl | rfl
  · simp only [zero_smul, add_zero]
  · rw [one_smul]
    change (QuotientGroup.mk' signsSubgroup)
      (golaySignHom (Multiplicative.ofAdd (golayEncoder.rangeRestrict (a + Pi.single 11 1)))) = _
    rw [map_add, omega_code, ofAdd_add, map_mul, map_mul,
      all_one_class, mul_one]
    rfl

/-- Every actual even-modulation Pauli choice projects to the intended original source sign. -/
theorem generatedSixth_sign_pauli_code_class (j : Fin 10) :
    (QuotientGroup.mk (golaySignIsometry (generatedSixthSignPauliCode j)) : Co1) =
      QuotientGroup.mk
        (golaySignIsometry (sourceGeneratedSignCode (generatedSixthMonomialSignCode j))) :=
  generatedSixth_sign_class_add_omega _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
