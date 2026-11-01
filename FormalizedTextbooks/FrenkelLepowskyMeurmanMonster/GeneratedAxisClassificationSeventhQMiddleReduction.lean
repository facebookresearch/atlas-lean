/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQTranslation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhTensorZeroCoefficient
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! Actual seventh-axis Q fixation reduces to pure modulation fixation of its genuine middle
    state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The nonzero actual zero-spin column coefficient forces central coefficient zero. -/
theorem generatedSeventh_Q_central_zero (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) : toAdd q.coeff = 0 := by
  have ht := generatedSeventh_Q_translation_zero q hq
  have he := generatedSpinSupport_fixed_phase q generatedSeventhTensorColumn 0
    (generatedSeventh_Q_tensor_column_fixed q hq)
    (fun t => by simp only [ht, add_zero, qSign_zero, one_mul])
    0 generatedSeventh_tensor_zero_nonzero
  simpa only [spinPhase, spinDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero] using he

/-- Every actual fixing extraspecial element is exactly a pure original cocode. -/
theorem generatedSeventh_Q_eq_cocode (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    q = cocodeQ (spinModulation q) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedSeventh_Q_translation_zero q hq, cocodeQ_translation]
  · rw [cocodeQ_modulation]
  · rw [generatedSeventh_Q_central_zero q hq, cocodeQ_coeff]

/-- Even original cocodes commute with actual triality, so the full middle vector is fixed. -/
theorem generatedSeventh_Q_middle_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    rhoLocal (inclQ q)
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) =
        rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis := by
  have he := monsterNortonEvenCocode_commute_extra (spinModulation q)
    (generatedSeventh_Q_modulation_even q hq)
  rw [← generatedSeventh_Q_eq_cocode q hq] at he
  apply sExtra.injective
  have hc := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace =>
    e (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) he.eq
  simp only [LinearEquiv.mul_apply] at hc
  rw [generatedSeventhAxis_local_expression] at hq
  exact hc.symm.trans hq

/-- The original nonzero spatial column extracts genuine middle spin-state fixation. -/
theorem generatedSeventh_Q_middle_spin_fixed (q : Q)
    (hq : rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis) :
    spinRepresentation q generatedSeventhSpinState = generatedSeventhSpinState := by
  have ht := ((generatedFourthQ_full_fixed_iff q
    (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).mp
      (generatedSeventh_Q_middle_fixed q hq)).2 16
  let k : ℝ := generatedOddTensorScale *
    generatedSeventhLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) 16
  have hk : k ≠ 0 := by
    have hc : generatedSeventhLocalFiber.val.2.val (Pi.single (0 : Fin 24) 1) 16 =
        (1 / 8 : ℝ) := by
      change leechIsomMatrix generatedSeventhLocalFiber.val.2 16 0 = _
      rw [generatedSeventh_forward_matrix_coordinate]
      have hh : generatedSeventhFrameVectorData 7 0 16 = 1 := by decide +kernel
      rw [hh]
      norm_num
    exact mul_ne_zero generatedOddTensorScale_ne_zero (by rw [hc]; norm_num)
  have he : (fun t => (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)).2.2 t 16) =
      k • generatedSeventhSpinState := by
    funext t
    rw [generatedSeventh_middle_tensor_rank_one]
    change generatedOddTensorScale * generatedSeventhSpinState t * _ =
      k * generatedSeventhSpinState t
    dsimp only [k]
    ring
  rw [he, map_smul] at ht
  ext t
  have h := congrFun ht t
  simp only [Pi.smul_apply, smul_eq_mul] at h
  exact mul_left_cancel₀ hk h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
