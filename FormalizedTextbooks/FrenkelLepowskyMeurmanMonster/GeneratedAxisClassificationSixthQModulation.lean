/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQMiddleReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQRootLower

/-! The actual spin support and evenness restrict the complete Q stabilizer to four cocodes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every selected translation has an actual nonzero middle-state coefficient. -/
theorem generatedSixth_spin_translation_nonzero (a : Fin 9 → ZMod 2) :
    generatedSixthSpinState (generatedSixthSpinPauliTranslationMatrix *ᵥ a) ≠ 0 := by
  have h := generatedSixth_spin_orbit_square_exact a
  have ht : generatedSixthSpinCoordinateOrbit 0 a =
      generatedSixthSpinPauliTranslationMatrix *ᵥ a := by
    change 0 + spinTranslation (generatedSixthSpinPauliProduct a) = _
    rw [zero_add, generatedSixth_spin_pauli_product_translation]
  rw [ht] at h
  intro hz
  rw [hz] at h
  norm_num at h

/-- Every original fixing Q modulation annihilates all nine actual translation columns. -/
theorem generatedSixth_Q_modulation_annihilates (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    spinModulation q ᵥ* generatedSixthSpinPauliTranslationMatrix = 0 := by
  funext j
  have ht := generatedSixth_Q_translation_zero q hq
  have hc := generatedSixth_Q_central_zero q hq
  have h := generatedSpinSupport_fixed_phase q generatedSixthSpinState 0
    (generatedSixth_Q_middle_spin_fixed q hq)
    (fun t => by simp only [ht, add_zero, qSign_zero, one_mul])
    (generatedSixthSpinPauliTranslationMatrix *ᵥ Pi.single j 1)
    (generatedSixth_spin_translation_nonzero (Pi.single j 1))
  rw [Matrix.mulVec_single_one] at h
  simpa only [spinPhase, hc, zero_add, add_zero, spinDot, Matrix.vecMul,
    dotProduct, Matrix.col, Matrix.transpose_apply, Pi.zero_apply] using h

private theorem binary_value : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide +kernel

/-- The genuine modulation is one of the four original rooted-plane cocodes. -/
theorem generatedSixth_Q_modulation_mem (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    ∃ j : Fin 4, spinModulation q = generatedSixthRootQModulation j := by
  let b := spinModulation q ᵥ* generatedSixthSpinSupportComplement
  have h := congrArg (fun M : Matrix (Fin 12) (Fin 12) (ZMod 2) => spinModulation q ᵥ* M)
    generatedSixth_spin_support_projection_certificate
  rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    generatedSixth_Q_modulation_annihilates q hq, Matrix.zero_vecMul,
    zero_add, Matrix.vecMul_one] at h
  change b ᵥ* generatedSixthSpinSupportMatrix = spinModulation q at h
  have hd : generatedSixthSpinSupportMatrix.col 11 = Pi.single (1 : Fin 3) 1 := by
    ext j
    fin_cases j <;> decide +kernel
  have hb : b 1 = 0 := by
    have he := congrFun h 11
    change b ⬝ᵥ generatedSixthSpinSupportMatrix.col 11 = spinModulation q 11 at he
    rw [hd, dotProduct_single, mul_one, generatedSixth_Q_modulation_even q hq] at he
    exact he
  have he : spinModulation q =
      b 0 • golayLabelCoefficients 1504 + b 2 • golayLabelCoefficients 912 := by
    funext i
    have hi := congrFun h i
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, hb, zero_mul, add_zero] at hi
    change b 0 * golayLabelCoefficients 1504 i + b 2 * golayLabelCoefficients 912 i = _ at hi
    exact hi.symm
  have hz : generatedSixthRootQModulation 0 = 0 := by decide +kernel
  have h1 : generatedSixthRootQModulation 1 = golayLabelCoefficients 1504 := rfl
  have h2 : generatedSixthRootQModulation 2 =
      golayLabelCoefficients 1504 + golayLabelCoefficients 912 := by decide +kernel
  have h3 : generatedSixthRootQModulation 3 = golayLabelCoefficients 912 := rfl
  rcases binary_value (b 0) with hb0 | hb0 <;> rcases binary_value (b 2) with hb2 | hb2
  · refine ⟨0, ?_⟩
    simpa only [hb0, hb2, zero_smul, add_zero, hz] using he
  · refine ⟨3, ?_⟩
    simpa only [hb0, hb2, zero_smul, one_smul, zero_add, h3] using he
  · refine ⟨1, ?_⟩
    simpa only [hb0, hb2, zero_smul, one_smul, add_zero, h1] using he
  · refine ⟨2, ?_⟩
    simpa only [hb0, hb2, one_smul, h2] using he

/-- Full genuine Q fixation is exhausted by the four previously proved fixing cocodes. -/
theorem generatedSixth_Q_fixed_mem (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    ∃ j : Fin 4, q = cocodeQ (generatedSixthRootQModulation j) := by
  obtain ⟨j, hj⟩ := generatedSixth_Q_modulation_mem q hq
  exact ⟨j, (generatedSixth_Q_eq_cocode q hq).trans (congrArg cocodeQ hj)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
