/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthAffinePauliModel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! A basis product reconstructs each genuine source pair lift without repeated word evaluation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Twelve literal pure modulation generators in the actual Pauli group. -/
def generatedSixthPairModulationBasis (j : Fin 12) : Q :=
  generatedAxisFourthQFromSpin 0 (Pi.single j 1) 0

private theorem modulation_prod (l : List Q) :
    spinModulation l.prod = (l.map spinModulation).sum := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [List.prod_cons, spinModulation_mul, ih, List.map_cons, List.sum_cons]

private theorem modulation_pow (q : Q) (n : ℕ) :
    spinModulation (q ^ n) = n • spinModulation q := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, spinModulation_mul, ih, succ_nsmul]

private theorem pure_pow (q : Q) (hq : spinTranslation q = 0)
    (hc : spinPhase q 0 = 0) (n : ℕ) :
    spinTranslation (q ^ n) = 0 ∧ spinPhase (q ^ n) 0 = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [pow_succ, spinTranslation_mul, spinPhase_mul, ih.1, zero_add, hq,
      add_zero, hc, ih.2]
    exact ⟨rfl, rfl⟩

private theorem pure_prod (l : List Q)
    (h : ∀ q ∈ l, spinTranslation q = 0 ∧ spinPhase q 0 = 0) :
    spinTranslation l.prod = 0 ∧ spinPhase l.prod 0 = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons q l ih =>
    have hq := h q (List.mem_cons_self ..)
    have hl := ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.prod_cons, spinTranslation_mul, spinPhase_mul, hq.1, hl.1,
      zero_add, hq.2, hl.2]
    exact ⟨trivial, trivial⟩

/-- The twelve basis powers reconstruct the original pure modulation, with central sign zero. -/
theorem generatedSixth_pair_modulation_product (m : SpinIndex) :
    generatedSixthAffinePauliProduct generatedSixthPairModulationBasis m =
      generatedAxisFourthQFromSpin 0 m 0 := by
  have hp : ∀ q ∈ List.ofFn
      (fun j : Fin 12 => generatedSixthPairModulationBasis j ^ (m j).val),
      spinTranslation q = 0 ∧ spinPhase q 0 = 0 := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    apply pure_pow
    · exact generatedAxisFourthQFromSpin_translation ..
    · simp only [generatedSixthPairModulationBasis, spinPhase,
        generatedAxisFourthQFromSpin_coeff, spinDot_zero_right, add_zero]
  have hprod := pure_prod _ hp
  apply generatedAxisFourthQ_spin_coordinates_injective
  · exact hprod.1.trans (generatedAxisFourthQFromSpin_translation ..).symm
  · unfold generatedSixthAffinePauliProduct
    rw [modulation_prod, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, modulation_pow, generatedSixthPairModulationBasis,
      generatedAxisFourthQFromSpin_modulation]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      ZMod.natCast_val, ZMod.cast_id, smul_eq_mul, Pi.single_apply]
    simp
  · simpa only [generatedSixthAffinePauliProduct, spinPhase, spinDot_zero_right, add_zero,
      generatedAxisFourthQFromSpin_coeff] using hprod.2

/-- Modulation followed by translation reconstructs the preferred zero-central lift. -/
theorem generatedSixth_pair_Q_product (u m : SpinIndex) :
    generatedSixthAffinePauliProduct generatedSixthPairModulationBasis m *
        generatedAxisFourthQFromSpin u 0 0 = generatedAxisFourthQFromSpin u m 0 := by
  rw [generatedSixth_pair_modulation_product]
  apply generatedAxisFourthQ_spin_coordinates_injective
  · simp only [spinTranslation_mul, generatedAxisFourthQFromSpin_translation, zero_add]
  · simp only [spinModulation_mul, generatedAxisFourthQFromSpin_modulation, add_zero]
  · have h : spinPhase (generatedAxisFourthQFromSpin 0 m 0 *
        generatedAxisFourthQFromSpin u 0 0) 0 = 0 := by
      rw [spinPhase_mul, generatedAxisFourthQFromSpin_translation]
      simp only [spinPhase, generatedAxisFourthQFromSpin_coeff, spinDot_zero_right, add_zero]
    simpa only [spinPhase, spinDot_zero_right, add_zero,
      generatedAxisFourthQFromSpin_coeff] using h

/-- Every actual Q homomorphism transports pair lifts by the twelve basis images. -/
theorem generatedSixth_pair_Q_image_product (φ : Q →* Q) (u m : SpinIndex) :
    φ (generatedAxisFourthQFromSpin u m 0) =
      generatedSixthAffinePauliProduct (fun j => φ (generatedSixthPairModulationBasis j)) m *
        φ (generatedAxisFourthQFromSpin u 0 0) := by
  rw [← generatedSixth_pair_Q_product, map_mul]
  congr 1
  simp only [generatedSixthAffinePauliProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  exact map_pow φ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
