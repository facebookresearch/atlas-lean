/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenCocode

/-! The three genuine rooted-plane short lifts fix the complete seventh axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

private theorem even_cocode_fixes_odd (m : SpinIndex) (hm : m 11 = 0) :
    rhoLocal (inclQ (cocodeQ m)) generatedOddAxis = generatedOddAxis := by
  have hs : spinRepresentation (cocodeQ m) (generatedOddSpinState 0 1 0) =
      generatedOddSpinState 0 1 0 := by
    change spinOperator (cocodeQ m) _ = _
    rw [generatedOddSpinState_pauli]
    simp only [cocodeQ_translation, cocodeQ_modulation, hm, zero_add,
      generatedOddSpinOutputSign, cocodeQ_coeff, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
    rfl
  have hq : cocodeQ m ∈ generatedOddSpinStateStabilizer := hs
  exact generatedOddSpinStateStabilizer_le_axis hq

private theorem cache_initial_cocode (j : Fin 3) :
    generatedSeventhQCache j 0 =
      cocodeQ (golayLabelCoefficients (generatedSeventhSourceModulation j)) := by
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

private theorem cache_final_cocode (j : Fin 3) :
    generatedSeventhQCache j 7 =
      cocodeQ (golayLabelCoefficients (generatedSeventhTargetModulation j)) := by
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext <;> decide +kernel

/-- The target preferred short lifts are the genuine even pure cocodes in source coordinates. -/
theorem generatedSeventh_target_pair_Q_cocode (j : Fin 3) :
    griessShortQ (Sum.inl (0, generatedSeventhTargetPair j)) =
      cocodeQ (golayLabelCoefficients (generatedSeventhTargetModulation j)) := by
  rw [← generatedSeventh_q_cache_final, cache_final_cocode]

private theorem transported_fix (f : localFiberSubgroup) (q : Q) (x : GriessSpace)
    (hq : rhoLocal (inclQ q) x = x) :
    rhoLocal (inclQ (spinConjugation f.val.1 q)) (rhoLocal (localFiberIntoH f) x) =
      rhoLocal (localFiberIntoH f) x := by
  have hc : inclQ (spinConjugation f.val.1 q) =
      localFiberIntoH f * inclQ q * (localFiberIntoH f)⁻¹ := by
    change QuotientGroup.mk' localDiagonalSubgroup
      (localFiberIncl (spinConjugation f.val.1 q)) = _
    rw [localFiberIncl_conjugate, map_mul, map_mul, map_inv]
    rfl
  rw [hc, map_mul, map_mul, map_inv]
  simp only [LinearEquiv.mul_apply]
  change rhoLocal (localFiberIntoH f)
    (rhoLocal (inclQ q) ((rhoLocal (localFiberIntoH f)).symm
      (rhoLocal (localFiberIntoH f) x))) = _
  rw [LinearEquiv.symm_apply_apply, hq]

/-- Each actual preferred short lift of the rooted plane fixes the whole seventh axis. -/
theorem generatedSeventh_target_pair_Q_fixed (j : Fin 3) :
    rhoLocal (inclQ (griessShortQ (Sum.inl (0, generatedSeventhTargetPair j))))
      generatedSeventhAxis = generatedSeventhAxis := by
  have hs : rhoLocal (inclQ (griessShortQ (Sum.inl (0, generatedSeventhSourcePair j))))
      generatedOddAxis = generatedOddAxis := by
    rw [← generatedSeventh_q_cache_initial, cache_initial_cocode]
    apply even_cocode_fixes_odd
    fin_cases j <;> decide +kernel
  have ht := transported_fix generatedSeventhLocalFiber
    (griessShortQ (Sum.inl (0, generatedSeventhSourcePair j))) generatedOddAxis hs
  rw [generatedSeventh_preferred_pair_transport] at ht
  have hc : Commute
      (rhoLocal (inclQ (griessShortQ (Sum.inl (0, generatedSeventhTargetPair j))))) sExtra := by
    rw [← generatedSeventh_q_cache_final, cache_final_cocode]
    apply monsterNortonEvenCocode_commute_extra
    fin_cases j <;> decide +kernel
  rw [generatedSeventhAxis_local_expression]
  have he := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace =>
    e (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) hc.eq
  change rhoLocal (inclQ (griessShortQ (Sum.inl (0, generatedSeventhTargetPair j))))
    (sExtra (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) =
      sExtra (rhoLocal
    (inclQ (griessShortQ (Sum.inl (0, generatedSeventhTargetPair j))))
    (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis)) at he
  rw [he, ht]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
