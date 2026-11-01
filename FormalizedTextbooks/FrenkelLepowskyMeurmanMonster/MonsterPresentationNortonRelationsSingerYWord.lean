/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full physical tensor binding of preferred source Y covariance under the actual Singer lift. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYCode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsYAllConjugation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check all physical signs, including the nonzero all-one-code components.
/-- The permuted physical code signs retain the full all-one correction. -/
theorem monsterNortonSingerY_basis_sign_certificate (a : Fin 11) (i : Fin 24) :
    golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisSource a))
      ((monsterNortonSingerPermutation 0).symm i) =
      golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisTarget a)) i +
        (monsterNortonSingerYBasisHigh a : ZMod 2) := by
  fin_cases a <;> fin_cases i <;> decide +kernel

private theorem low_y_tensor (a : Fin 2048) (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode ((y555NortonActualY ⟨a.val, by omega⟩ 0).val x)).2.2 t i =
      qSign (golayEncoder (monsterNortonYCode a) i) *
        (monsterNortonYSpin a).val (fun u => (griessConwayEncode x).2.2 u i) t := by
  rw [y555NortonActualY_word]
  exact monsterNortonYAllWord_tensor a x t i

private theorem central_tensor (x : GriessSpace) :
    (griessConwayEncode ((qIntoGenerated qCentralInvolution).val x)).2.2 =
      -(griessConwayEncode x).2.2 := by
  change (griessConwayEncode (localCentralGriess x)).2.2 = _
  rw [localCentralGriess_encode]

private theorem generated_mul_apply (g h : G) (x : GriessSpace) :
    (g * h).val x = g.val (h.val x) := rfl

private theorem full_y_tensor (a : Fin 11) (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode
      ((y555NortonActualY (monsterNortonSingerYBasisFull a) 0).val x)).2.2 t i =
      qSign (golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisSource a))
        ((monsterNortonSingerPermutation 0).symm i)) *
        (monsterNortonYSpin (monsterNortonSingerYBasisTarget a)).val
          (fun u => (griessConwayEncode x).2.2 u i) t := by
  have he := monsterNortonSourceY_of_omega_decomposition _ _ _
    (monsterNortonSingerYBasisFull_decomposition a)
  have hh : monsterNortonSingerYBasisHigh a = 0 ∨
      monsterNortonSingerYBasisHigh a = 1 := by
    fin_cases a <;> decide +kernel
  rw [monsterNortonSingerY_basis_sign_certificate, qSign_add]
  rcases hh with hh | hh
  · rw [hh, pow_zero, mul_one] at he
    rw [he, low_y_tensor]
    simp only [hh, Nat.cast_zero, qSign_zero, mul_one]
  · rw [hh, pow_one] at he
    rw [he, generated_mul_apply, low_y_tensor]
    have hx : (fun u =>
        (griessConwayEncode ((qIntoGenerated qCentralInvolution).val x)).2.2 u i) =
          -(fun u => (griessConwayEncode x).2.2 u i) := by
      funext u
      rw [central_tensor]
      rfl
    rw [hx, map_neg, hh]
    simp only [Pi.neg_apply, Nat.cast_one, qSign_one]
    ring

/-- The genuine Singer lift intertwines the complete literal source Y words. -/
theorem monsterNortonSingerLocal_generated_Y_basis (a : Fin 11) :
    localIntoGenerated monsterNortonSingerLocal *
      y555NortonActualY ⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ 0 =
      y555NortonActualY (monsterNortonSingerYBasisFull a) 0 *
        localIntoGenerated monsterNortonSingerLocal := by
  obtain ⟨h, hh⟩ := monsterSourceY_word_mem_local
    ⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ 0
  obtain ⟨k, hk⟩ := monsterSourceY_word_mem_local (monsterNortonSingerYBasisFull a) 0
  have hT (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
      (griessConwayEncode (rhoLocal h x)).2.2 t i =
        qSign (golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisSource a)) i) *
          (monsterNortonYSpin (monsterNortonSingerYBasisSource a)).val
            (fun u => (griessConwayEncode x).2.2 u i) t := by
    change (griessConwayEncode ((localIntoGenerated h).val x)).2.2 t i = _
    rw [hh]
    exact low_y_tensor _ x t i
  have kT (x : GriessSpace) (t : SpinIndex) (i : Fin 24) :
      (griessConwayEncode (rhoLocal k x)).2.2 t i =
        qSign (golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisSource a))
          ((monsterNortonSingerPermutation 0).symm i)) *
          (monsterNortonYSpin (monsterNortonSingerYBasisTarget a)).val
            (fun u => (griessConwayEncode x).2.2 u i) t := by
    change (griessConwayEncode ((localIntoGenerated k).val x)).2.2 t i = _
    rw [hk]
    exact full_y_tensor a x t i
  have he : monsterNortonSingerLocal * h = k * monsterNortonSingerLocal := by
    apply monsterLocalTensor_identifies
    intro x
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    funext t i
    rw [monsterNortonSingerLocal_tensor, hT, kT]
    have hf : (fun u => (griessConwayEncode (rhoLocal monsterNortonSingerLocal x)).2.2 u i) =
        monsterNortonSingerSpin.val
          (fun u => (griessConwayEncode x).2.2 u
            ((monsterNortonSingerPermutation 0).symm i)) := by
      funext u
      exact monsterNortonSingerLocal_tensor x u i
    rw [hf]
    have hs := congrArg (fun s : SpinHolomorph =>
      s.val (fun u => (griessConwayEncode x).2.2 u
        ((monsterNortonSingerPermutation 0).symm i)) t)
      (monsterNortonSingerY_basis_spin a)
    exact congrArg (fun z : ℝ =>
      qSign (golayEncoder (monsterNortonYCode (monsterNortonSingerYBasisSource a))
        ((monsterNortonSingerPermutation 0).symm i)) * z) hs
  have hG := congrArg localIntoGenerated he
  simpa only [map_mul, hh, hk] using hG

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
