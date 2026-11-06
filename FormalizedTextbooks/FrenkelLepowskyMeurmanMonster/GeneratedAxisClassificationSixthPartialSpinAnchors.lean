/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPartialPauliState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPartialPhaseInteger

/-! The original nine spin anchor coefficients follow from bounded signed source evaluations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual anchor coefficient at each original spin-word stage. -/
def generatedSixthPartialSpinAnchor (k : Fin 9) : ℝ :=
  generatedSixthPartialSpinState k (golayLabelCoefficients (generatedSixthPartialAnchor k))

/-- The genuine phase model embeds as its actual anchor times a signed integer vector. -/
theorem generatedSixth_partial_phase_embed (k : Fin 9) :
    generatedSixthPartialSpinState k =
      generatedSixthPartialSpinAnchor k •
        nortonUIntegerEmbed (generatedSixthPartialPhaseInteger k) := by
  ext t
  rw [generatedSixth_partial_phase_model]
  simp only [generatedSixthPartialSpinAnchor, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed, generatedSixthPartialPhaseInteger, nortonUIntegerLabel_inverse,
    Int.cast_ite, Int.cast_zero, nortonUIntegerSign_real]
  exact mul_comm _ _

/-- The next operator for arbitrary spin normalizers with the source word pattern. -/
def generatedSixthPartialStepOf (p q x : SpinHolomorph) : Fin 8 → SpinHolomorph :=
  ![p,x,p,q,p,x,q,x]

/-- The next genuine original spin operator at each prefix. -/
def generatedSixthPartialSpinStep : Fin 8 → SpinHolomorph :=
  generatedSixthPartialStepOf (monsterSourcePermutationSpin 0)
    (monsterSourcePermutationSpin 1) xiSpinHolomorph

private theorem prefix_step (p q x : SpinHolomorph) (k : Fin 8) :
    generatedSixthPartialWordOf p q x k.succ =
      generatedSixthPartialStepOf p q x k * generatedSixthPartialWordOf p q x (Fin.castSucc k) := by
  fin_cases k
  · change p = p * 1
    exact (mul_one p).symm
  all_goals rfl

/-- The prefix states advance by the actual source spin operators. -/
theorem generatedSixth_partial_spin_step (k : Fin 8) :
    generatedSixthPartialSpinState k.succ =
      (generatedSixthPartialSpinStep k).val
        (generatedSixthPartialSpinState (Fin.castSucc k)) :=
  congrArg (fun s : SpinHolomorph => s.val (generatedOddSpinState 0 1 0))
    (prefix_step (monsterSourcePermutationSpin 0) (monsterSourcePermutationSpin 1)
      xiSpinHolomorph k)

/-- The integer step has the exact denominator of the original permutation or Gaussian. -/
theorem generatedSixth_partial_step_embed (k : Fin 8) (v : NortonUIntegerVector) :
    (generatedSixthPartialSpinStep k).val (nortonUIntegerEmbed v) =
      (1 / (generatedSixthPartialDenominator k : ℝ)) •
        nortonUIntegerEmbed (generatedSixthPartialIntegerStep k v) := by
  fin_cases k
  all_goals simp only [generatedSixthPartialSpinStep, generatedSixthPartialStepOf,
    generatedSixthPartialDenominator, generatedSixthPartialIntegerStep,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Nat.cast_one, div_one, one_smul]
  · exact generatedSixth_integer_permutation_embed 0 v
  · exact nortonUIntegerXi_embed v
  · exact generatedSixth_integer_permutation_embed 0 v
  · exact generatedSixth_integer_permutation_embed 1 v
  · exact generatedSixth_integer_permutation_embed 0 v
  · exact nortonUIntegerXi_embed v
  · exact generatedSixth_integer_permutation_embed 1 v
  · exact nortonUIntegerXi_embed v

/-- Every genuine anchor advances by its checked finite signed numerator. -/
theorem generatedSixth_partial_anchor_recurrence (k : Fin 8) :
    generatedSixthPartialSpinAnchor k.succ =
      ((generatedSixthPartialAnchorNumerator k : ℤ) : ℝ) /
        (generatedSixthPartialDenominator k : ℝ) *
      generatedSixthPartialSpinAnchor (Fin.castSucc k) := by
  change generatedSixthPartialSpinState k.succ
    (golayLabelCoefficients (generatedSixthPartialAnchor k.succ)) = _
  conv_lhs =>
    rw [generatedSixth_partial_spin_step, generatedSixth_partial_phase_embed,
      map_smul, generatedSixth_partial_step_embed, smul_smul]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, nortonUIntegerLabel_coeff]
  change generatedSixthPartialSpinAnchor (Fin.castSucc k) *
      (1 / (generatedSixthPartialDenominator k : ℝ)) *
      (generatedSixthPartialAnchorNumerator k : ℝ) = _
  ring

/-- The initial actual anchor has the original coefficient one. -/
theorem generatedSixth_partial_anchor_zero : generatedSixthPartialSpinAnchor 0 = 1 := by
  change generatedOddSpinState 0 1 0 (golayLabelCoefficients 0) = 1
  have hz : golayLabelCoefficients 0 = 0 := by decide +kernel
  rw [hz]
  have hl : generatedOddSpinLow (0 : SpinIndex) = 0 := rfl
  simp only [generatedOddSpinState, hl, ite_true, Pi.zero_apply,
    mul_zero, add_zero, qSign_zero]

/-- All original anchor coefficients, including their actual scalar signs. -/
theorem generatedSixth_partial_anchor_values (k : Fin 9) :
    generatedSixthPartialSpinAnchor k =
      (![1,1,-1/4,-1/4,-1/4,-1/4,1/8,-1/8,1/16] k : ℝ) := by
  have h1 := generatedSixth_partial_anchor_recurrence 0
  have h2 := generatedSixth_partial_anchor_recurrence 1
  have h3 := generatedSixth_partial_anchor_recurrence 2
  have h4 := generatedSixth_partial_anchor_recurrence 3
  have h5 := generatedSixth_partial_anchor_recurrence 4
  have h6 := generatedSixth_partial_anchor_recurrence 5
  have h7 := generatedSixth_partial_anchor_recurrence 6
  have h8 := generatedSixth_partial_anchor_recurrence 7
  simp only [generatedSixth_partial_anchor_certificate] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num [generatedSixthPartialDenominator, generatedSixth_partial_anchor_zero] at h1 h2 h3 h4
  norm_num [generatedSixthPartialDenominator, generatedSixth_partial_anchor_zero] at h5 h6 h7 h8
  fin_cases k <;> norm_num [h1,h2,h3,h4,h5,h6,h7,h8, generatedSixth_partial_anchor_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
