/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQTranslation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSpinSupportPhases

/-! Actual signed periods and all support-difference phase constraints of the fifth tensor. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- Every original fifth tensor column is anti-periodic under the genuine all-one spin shift. -/
theorem generatedFifth_tensor_add_omega (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.2 (t + Pi.single 11 1) i =
      -(griessConwayEncode generatedFifthAxis).2.2 t i := by
  rw [generatedFifth_tensor_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    trialityYTensor_add_omega, mul_neg, Finset.sum_neg_distrib]

/-- Every listed low dictionary coordinate is a genuine nonzero original tensor entry. -/
theorem generatedFifth_tensor_low_nonzero (j : Fin 64) :
    (griessConwayEncode generatedFifthAxis).2.2
      (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1)
        (generatedFifthOddRootOutputData j).2 ≠ 0 := by
  rw [generatedFifth_tensor_nonzero_iff, generatedFifth_spin_low_dictionary]
  exact ⟨j, rfl⟩

/-- Actual tensor fixation supplies one common signed translation period for every column. -/
theorem generatedFifth_tensor_signed_period (q : Q)
    (hq : ∀ i : Fin 24, spinRepresentation q
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
        (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i)) :
    ∃ c : ZMod 2, ∀ t : SpinIndex, ∀ i : Fin 24,
      (griessConwayEncode generatedFifthAxis).2.2 (t + spinTranslation q) i =
        qSign c * (griessConwayEncode generatedFifthAxis).2.2 t i := by
  rcases generatedFifth_tensor_translation q hq with h | h
  · refine ⟨0, ?_⟩
    simp only [h, add_zero, qSign_zero, one_mul, implies_true]
  · refine ⟨1, ?_⟩
    simp only [h, generatedFifth_tensor_add_omega, qSign_one, neg_one_mul, implies_true]

/-- Genuine fixation forces modulation to annihilate every listed dictionary difference. -/
theorem generatedFifth_tensor_modulation_differences (q : Q)
    (hq : ∀ i : Fin 24, spinRepresentation q
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
        (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i)) (j : Fin 64) :
    spinDot (spinModulation q)
      (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
        generatedFifthSpinLow (generatedFifthColumnLabels 0)) = 0 := by
  obtain ⟨c, hc⟩ := generatedFifth_tensor_signed_period q hq
  have hj := generatedSpinSupport_fixed_phase q
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t
      (generatedFifthOddRootOutputData j).2) c (hq _) (fun t => hc t _)
      _ (generatedFifth_tensor_low_nonzero j)
  have h0 := generatedSpinSupport_fixed_phase q
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t
      (generatedFifthOddRootOutputData 0).2) c (hq _) (fun t => hc t _)
      _ (generatedFifth_tensor_low_nonzero 0)
  have he := add_left_cancel (add_right_cancel (hj.trans h0.symm))
  change spinDot (spinModulation q)
    (generatedFifthSpinLow (generatedFifthOddRootOutputData j).1) =
      spinDot (spinModulation q)
        (generatedFifthSpinLow (generatedFifthOddRootOutputData 0).1) at he
  have href : (generatedFifthOddRootOutputData 0).1 = generatedFifthColumnLabels 0 := by rfl
  rw [href] at he
  rw [spinDot_add_right, he, ZModModule.add_self]

/-- Genuine tensor fixation forces zero modulation on the all-one spin coordinate. -/
theorem generatedFifth_tensor_modulation_omega (q : Q)
    (hq : ∀ i : Fin 24, spinRepresentation q
      (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
        (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i)) :
    spinModulation q 11 = 0 := by
  obtain ⟨c, hc⟩ := generatedFifth_tensor_signed_period q hq
  let t0 := generatedFifthSpinLow (generatedFifthOddRootOutputData 0).1
  let i0 := (generatedFifthOddRootOutputData 0).2
  have ht : (griessConwayEncode generatedFifthAxis).2.2 t0 i0 ≠ 0 :=
    generatedFifth_tensor_low_nonzero 0
  have hu : (griessConwayEncode generatedFifthAxis).2.2
      (t0 + Pi.single 11 1) i0 ≠ 0 := by
    rw [generatedFifth_tensor_add_omega]
    exact neg_ne_zero.mpr ht
  have he := generatedSpinSupport_fixed_modulation_difference q
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i0) c (hq i0)
      (fun t => hc t i0) t0 (t0 + Pi.single 11 1) ht hu
  rw [← add_assoc, ZModModule.add_self, zero_add] at he
  simpa only [spinDot, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
