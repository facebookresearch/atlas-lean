/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MutualInformation

@[expose] public section

/-!
# Tests for finite mutual information in nats

The fair copy law (`Y = X` for a fair bit) has mutual information
`Real.log 2`: the coordinates are fully dependent, the marginals are
fair, and the joint law carries one bit. Product laws have zero mutual
information, including a product law with zero-mass atoms.
-/

set_option autoImplicit false

open InformationTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.MutualInformation

/-- A fair coin. -/
noncomputable def fair : PMF Bool :=
  PMF.ofFintype (fun _ ↦ ((1 / 2 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_inj, add_halves])

/-- A coin biased towards `true` with probability `3 / 4`. -/
noncomputable def biased : PMF Bool :=
  PMF.ofFintype (fun b ↦ ((cond b (3 / 4) (1 / 4) : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, ← ENNReal.coe_add, ← ENNReal.coe_one,
      ENNReal.coe_inj, ← NNReal.coe_inj]
    push_cast
    norm_num)

theorem fair_apply (b : Bool) : (fair b).toReal = 1 / 2 := by
  simp [fair]

/-- The fair copy law: `Y = X` for a fair bit. -/
noncomputable def copyLaw : PMF (Bool × Bool) :=
  PMF.ofFintype (fun z ↦ if z.1 = z.2 then ((1 / 2 : ℝ≥0) : ℝ≥0∞) else 0) (by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    rw [show (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 2 * (2 : ℝ≥0∞)⁻¹ by ring,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)])

theorem copyLaw_apply (z : Bool × Bool) :
    (copyLaw z).toReal = if z.1 = z.2 then 1 / 2 else 0 := by
  by_cases h : z.1 = z.2 <;> simp [copyLaw, h]

theorem negMulLog_half : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
  rw [Real.negMulLog, one_div, Real.log_inv]
  ring

/-- A fair coin carries one bit. -/
theorem shannonEntropy_fair : shannonEntropy fair = 1 := by
  rw [shannonEntropy, Fintype.sum_bool, fair_apply, fair_apply]
  simp only [Real.negMulLog, one_div, Real.log_inv]
  field_simp
  ring

/-- The copy law carries one bit: only the two diagonal atoms have mass. -/
theorem shannonEntropy_copyLaw : shannonEntropy copyLaw = 1 := by
  rw [shannonEntropy]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, copyLaw_apply]
  norm_num [negMulLog_half]

theorem copyLaw_map_fst : copyLaw.map Prod.fst = fair := by
  ext a
  rw [map_fst_apply, Fintype.sum_bool]
  cases a <;> simp [fair, copyLaw]

theorem copyLaw_map_snd : copyLaw.map Prod.snd = fair := by
  ext b
  rw [map_snd_apply, Fintype.sum_bool]
  cases b <;> simp [fair, copyLaw]

/-- The copy law has one bit of mutual information. -/
theorem finiteMutualInformation_copyLaw : finiteMutualInformation copyLaw = 1 := by
  rw [finiteMutualInformation_eq, copyLaw_map_fst, copyLaw_map_snd,
    shannonEntropy_fair, shannonEntropy_copyLaw]
  norm_num

/-- The fair copy law has mutual information `Real.log 2` nats. -/
theorem mutualInfo_copyLaw : mutualInfo copyLaw = Real.log 2 := by
  rw [mutualInfo_eq_finiteMutualInformation, finiteMutualInformation_copyLaw, one_mul]

/-- A concrete product law has zero mutual information. -/
example : mutualInfo (prodJoint fair biased) = 0 :=
  mutualInfo_prodJoint fair biased

/-- A product law with zero-mass atoms has zero mutual information. -/
example : mutualInfo (prodJoint (PMF.pure false) (PMF.pure true)) = 0 :=
  mutualInfo_prodJoint _ _

/-- Zero-mass arithmetic in a product law: the off-diagonal atom
`(false, false)` of `pure false × pure true` has mass `0`. -/
example : (prodJoint (PMF.pure false) (PMF.pure true)) (false, false) = 0 := by
  rw [prodJoint_apply]
  simp

/-- Mutual information is nonnegative on the copy law, with the exact value. -/
example : 0 ≤ mutualInfo copyLaw := by
  rw [mutualInfo_copyLaw]
  exact Real.log_nonneg one_le_two

/-- Swapping the coordinates of the copy law does not change its
mutual information. -/
example : mutualInfo (copyLaw.map fun z => (z.2, z.1)) = Real.log 2 := by
  rw [mutualInfo_swap, mutualInfo_copyLaw]

end MathlibExtTest.InformationTheory.MutualInformation
