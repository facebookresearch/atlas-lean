/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Exact coordinate units for the original fifth tensor, retaining all source signs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Both actual spin addresses over an original odd dictionary row. -/
def generatedFifthXiTensorAddress (j : Fin 64) (b : ZMod 2) : SpinIndex :=
  generatedFifthSpinLow (generatedFifthOddRootOutputData j).1 +
    b • (Pi.single 11 1 : SpinIndex)

/-- The signed unit weight contains the input, preferred-Q, physical-mask and all-one phases. -/
def generatedFifthXiTensorWeight (j : Fin 64) (b : ZMod 2) : ℤ :=
  nortonUIntegerSign (generatedFifthOddCoefficientPhaseData j +
    golayBooleanCast ((golayEncodedMask (generatedFifthOddRootOutputData j).1.val).testBit
      (generatedFifthOddRootOutputData j).2.val) + b)

/-- Both support addresses have precisely the original low dictionary label. -/
theorem generatedFifth_xi_address_dictionary (j : Fin 64) (b : ZMod 2) :
    spinDictionaryCode (generatedFifthXiTensorAddress j b) =
      (generatedFifthOddRootOutputData j).1 := by
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · simp only [generatedFifthXiTensorAddress, zero_smul, add_zero,
      generatedFifth_spin_low_dictionary]
  · simp only [generatedFifthXiTensorAddress, one_smul,
      spinDictionaryCode_add_omega, generatedFifth_spin_low_dictionary]

/-- The last bit of a support address is its displayed all-one bit. -/
theorem generatedFifth_xi_address_last (j : Fin 64) (b : ZMod 2) :
    generatedFifthXiTensorAddress j b 11 = b := by
  simp only [generatedFifthXiTensorAddress, Pi.add_apply, generatedFifth_spin_low_last,
    Pi.smul_apply, Pi.single_apply, ite_true, smul_eq_mul, mul_one, zero_add]

/-- The 64 genuine low dictionary labels in this tensor are distinct. -/
theorem generatedFifth_xi_low_labels_injective : Function.Injective
    (fun j : Fin 64 => (generatedFifthOddRootOutputData j).1) := by
  decide +kernel

/-- Every original tensor coordinate at a listed address has the exact signed unit weight. -/
theorem generatedFifth_xi_address_value (j : Fin 64) (b : ZMod 2) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.2 (generatedFifthXiTensorAddress j b) i =
      if i = (generatedFifthOddRootOutputData j).2 then
        (generatedFifthXiTensorWeight j b : ℝ) / Real.sqrt 2 else 0 := by
  classical
  rw [generatedFifth_tensor_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp only [trialityYTensor, generatedFifth_xi_address_dictionary,
      generatedFifth_xi_address_last, ite_true, mul_one,
      generatedFifthXiTensorWeight, nortonUIntegerSign_real, qSign_add]
    cases h : (golayEncodedMask (generatedFifthOddRootOutputData j).1.val).testBit
        (generatedFifthOddRootOutputData j).2.val <;>
      by_cases hi : i = (generatedFifthOddRootOutputData j).2 <;>
        simp [hi, golayBooleanCast, qSign_zero, qSign_one] <;> ring
  · intro k _ hkj
    have hd : (generatedFifthOddRootOutputData j).1 ≠
        (generatedFifthOddRootOutputData k).1 := by
      intro hd
      exact hkj (generatedFifth_xi_low_labels_injective hd.symm)
    simp [trialityYTensor, generatedFifth_xi_address_dictionary, hd]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- Distinct original support labels and all-one bits have distinct spin addresses. -/
theorem generatedFifth_xi_addresses_injective : Function.Injective
    (fun p : Fin 64 × ZMod 2 => generatedFifthXiTensorAddress p.1 p.2) := by
  intro p q h
  have hj : p.1 = q.1 := generatedFifth_xi_low_labels_injective (by
    simpa only [generatedFifth_xi_address_dictionary] using congrArg spinDictionaryCode h)
  have hb : p.2 = q.2 := by
    simpa only [generatedFifth_xi_address_last] using congrFun h 11
  exact Prod.ext hj hb

/-- Each actual original spin column is the exact sum of its 128 signed coordinate units. -/
theorem generatedFifth_xi_tensor_units (i : Fin 24) :
    (fun t => (griessConwayEncode generatedFifthAxis).2.2 t i) =
      ∑ j : Fin 64, ∑ b : ZMod 2,
        (if i = (generatedFifthOddRootOutputData j).2 then
          (generatedFifthXiTensorWeight j b : ℝ) / Real.sqrt 2 else 0) •
            (Pi.single (generatedFifthXiTensorAddress j b) 1 : SpinSpace) := by
  classical
  simp_rw [← generatedFifth_xi_address_value]
  rw [← Fintype.sum_prod_type (f := fun p : Fin 64 × ZMod 2 =>
    (griessConwayEncode generatedFifthAxis).2.2 (generatedFifthXiTensorAddress p.1 p.2) i •
      (Pi.single (generatedFifthXiTensorAddress p.1 p.2) 1 : SpinSpace))]
  funext t
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases ht : (griessConwayEncode generatedFifthAxis).2.2 t i = 0
  · rw [ht]
    symm
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : t = generatedFifthXiTensorAddress p.1 p.2
    · simp only [hp, ite_true, mul_one]
      exact hp ▸ ht
    · simp only [hp, ite_false, mul_zero]
  · obtain ⟨j, hj⟩ := (generatedFifth_tensor_nonzero_iff t i).mp ht
    obtain ⟨b, hb⟩ := generatedFifth_spin_dictionary_decomposition t
    have hd := congrArg Prod.fst hj
    have he : t = generatedFifthXiTensorAddress j b := by
      simpa only [generatedFifthXiTensorAddress, hd] using hb
    symm
    rw [Finset.sum_eq_single (j, b)]
    · simp only [he, ite_true, mul_one]
    · intro p _ hp
      have hn : t ≠ generatedFifthXiTensorAddress p.1 p.2 := by
        intro hh
        exact hp (generatedFifth_xi_addresses_injective (hh.symm.trans he))
      simp only [hn, ite_false, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
