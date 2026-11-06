/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivity

/-! The actual signed-short orbit anchor in Höhn–Seysen, arXiv:2508.01037,
Lemma 3.3. The label action and both signs are obtained from the genuine local
fiber action, concrete Leech transitivity, and extraspecial phase correction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

private theorem short_unit_image (f : localFiberSubgroup) (r : GriessShortIndex) :
    localShortRepresentation f (Pi.single r (1 : ℝ)) =
      qSign (localShortPhase f r) • Pi.single (griessShortPermutation f.val.2 r) 1 := by
  funext t
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective t
  change localShortOperator f (Pi.single r 1) (griessShortPermutation f.val.2 s) = _
  rw [localShortOperator_image]
  by_cases h : s = r
  · subst s
    simp
  · have hp : griessShortPermutation f.val.2 s ≠ griessShortPermutation f.val.2 r :=
      fun he => h ((griessShortPermutation f.val.2).injective he)
    simp [h, hp]

/-- The actual fiber action transports both the short label and its binary sign. -/
theorem generatedAxis_localFiber_image (f : localFiberSubgroup)
    (r : GriessShortIndex) (c : ZMod 2) :
    localGriessRepresentation f (conwayShortAxis r c) =
      conwayShortAxis (griessShortPermutation f.val.2 r) (localShortPhase f r + c) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [localGriessRepresentation_encode, conwayShortAxis_encode, conwayShortAxis_encode,
    localConwayRawRepresentation_apply]
  simp only [conwayShortAxisRaw, map_smul, conwayMatrixAction_short_outer,
    short_unit_image, map_zero, smul_smul, qSign_add]
  congr 3
  ring

/-- The two signs of every genuine short label are in one actual local H orbit. -/
theorem generatedAxis_local_signed_transitive (r s : GriessShortIndex) (c d : ZMod 2) :
    ∃ h : H, rhoLocal h (conwayShortAxis r c) = conwayShortAxis s d := by
  obtain ⟨e, _, he⟩ := leechShort_concrete_label_transitive r s
  obtain ⟨f, hf⟩ := generatedCentral_localFiber_lift e
  have hp : griessShortPermutation f.val.2 r = s := by rw [hf]; exact he
  obtain ⟨q, hq⟩ := localAxisQPhase_surjective s
    (ofAdd (d + localShortPhase f r + c))
  have hphase : localShortPhase (localFiberIncl q * f) r + c = d := by
    rw [localShortPhase_mul, hp, localAxisQPhase_eq_short_phase, hq]
    simp only [toAdd_ofAdd]
    have hx : localShortPhase f r + localShortPhase f r = 0 := CharTwo.add_self_eq_zero _
    have hc : c + c = 0 := CharTwo.add_self_eq_zero _
    linear_combination hx + hc
  refine ⟨localFiberIntoH (localFiberIncl q * f), ?_⟩
  change localGriessRepresentation (localFiberIncl q * f) _ = _
  rw [generatedAxis_localFiber_image, hphase]
  have hlabel : griessShortPermutation (localFiberIncl q * f).val.2 r = s := by
    change griessShortPermutation (1 * f.val.2) r = s
    simpa only [one_mul] using hp
  rw [hlabel]

/-- The explicit label and binary sign uniquely determine the actual axis. -/
theorem generatedAxis_signed_injective : Function.Injective
    (fun p : GriessShortIndex × ZMod 2 => conwayShortAxis p.1 p.2) := by
  rintro ⟨r, c⟩ ⟨s, d⟩ h
  have he := congrArg (fun x : GriessSpace => (griessConwayEncode x).2.1 r) h
  rw [conwayShortAxis_encode, conwayShortAxis_encode] at he
  have hrs : r = s := by
    by_contra hrs
    simp only [conwayShortAxisRaw, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hrs, mul_one, mul_zero] at he
    have hc := qSign_sq c
    nlinarith
  subst s
  have hcd : c = d := by
    simp only [conwayShortAxisRaw, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      mul_one] at he
    fin_cases c <;> fin_cases d
    all_goals norm_num [qSign] at he
    all_goals rfl
  exact congrArg (fun a : ZMod 2 => (r, a)) hcd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
