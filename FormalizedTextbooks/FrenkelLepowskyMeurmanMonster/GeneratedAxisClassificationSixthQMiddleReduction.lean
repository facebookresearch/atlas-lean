/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQTranslation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorZeroCoefficient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! Actual sixth-axis Q fixation reduces to pure modulation fixation of its genuine middle state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The nonzero actual zero-spin column coefficient forces central coefficient zero. -/
theorem generatedSixth_Q_central_zero (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) : toAdd q.coeff = 0 := by
  have ht := generatedSixth_Q_translation_zero q hq
  have he := generatedSpinSupport_fixed_phase q generatedSixthTensorColumn 0
    (generatedSixth_Q_tensor_column_fixed q hq)
    (fun t => by simp only [ht, add_zero, qSign_zero, one_mul])
    0 generatedSixth_tensor_zero_nonzero
  simpa only [spinPhase, spinDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero] using he

/-- Every actual fixing extraspecial element is exactly a pure original cocode. -/
theorem generatedSixth_Q_eq_cocode (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    q = cocodeQ (spinModulation q) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedSixth_Q_translation_zero q hq, cocodeQ_translation]
  · rw [cocodeQ_modulation]
  · rw [generatedSixth_Q_central_zero q hq, cocodeQ_coeff]

/-- Even original cocodes commute with actual triality, so the full middle vector is fixed. -/
theorem generatedSixth_Q_middle_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    rhoLocal (inclQ q)
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis) =
        rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis := by
  have he := monsterNortonEvenCocode_commute_extra (spinModulation q)
    (generatedSixth_Q_modulation_even q hq)
  rw [← generatedSixth_Q_eq_cocode q hq] at he
  apply sExtra.injective
  have hc := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace =>
    e (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)) he.eq
  simp only [LinearEquiv.mul_apply] at hc
  rw [generatedSixthAxis_local_expression] at hq
  exact hc.symm.trans hq

/-- The original nonzero spatial column extracts genuine middle spin-state fixation. -/
theorem generatedSixth_Q_middle_spin_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSixthAxis = generatedSixthAxis) :
    spinRepresentation q generatedSixthSpinState = generatedSixthSpinState := by
  have ht := ((generatedFourthQ_full_fixed_iff q
    (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).mp
      (generatedSixth_Q_middle_fixed q hq)).2 16
  let k : ℝ := generatedOddTensorScale *
    generatedSixthLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) 16
  have hk : k ≠ 0 := by
    have hc : generatedSixthLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) 16 =
        (-3 / 8 : ℝ) := by
      change leechIsomMatrix generatedSixthLocalFiber.val.2 16 0 = _
      rw [generatedSixth_forward_matrix_coordinate]
      have hh : generatedSixthFrameVectorData 8 0 16 = -3 := by decide +kernel
      rw [hh]
      norm_num
    exact mul_ne_zero generatedOddTensorScale_ne_zero (by rw [hc]; norm_num)
  have he : (fun t => (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.2 t 16) =
      k • generatedSixthSpinState := by
    funext t
    rw [generatedSixth_middle_tensor_rank_one]
    change generatedOddTensorScale * generatedSixthSpinState t * _ = k * generatedSixthSpinState t
    dsimp only [k]
    ring
  rw [he, map_smul] at ht
  ext t
  have h := congrFun ht t
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hk h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
