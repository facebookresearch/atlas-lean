/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadEnumeration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhase6

/-! Actual preferred-Q phases, normalized coefficients and complete octad support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All finite phases and coefficient numerators agree with the original full-Q formula. -/
theorem generatedSixth_middle_octad_phase_weight_certificate (k : Fin 273) :
    Multiplicative.toAdd (generatedSixthPairQImage (generatedSixthMiddleOctadInput k).1
      (griessPairSyndrome (generatedSixthMiddleOctadInput k).2)).coeff =
        generatedSixthMiddleOctadPhase k ∧
      (if generatedSixthMiddleOctadPhase k = 0 then
        generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput k) else
        -generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput k)) =
          generatedSixthMiddleOctadWeight k := by
  by_cases hk0 : k.val < 39
  · have hj : k.val - 0 < 39 := by omega
    have hn : (⟨0 + (k.val - 0), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 0 + (k.val - 0) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate0
      (⟨k.val - 0, hj⟩ : Fin 39)
  by_cases hk1 : k.val < 78
  · have hj : k.val - 39 < 39 := by omega
    have hn : (⟨39 + (k.val - 39), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 39 + (k.val - 39) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate1
      (⟨k.val - 39, hj⟩ : Fin 39)
  by_cases hk2 : k.val < 117
  · have hj : k.val - 78 < 39 := by omega
    have hn : (⟨78 + (k.val - 78), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 78 + (k.val - 78) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate2
      (⟨k.val - 78, hj⟩ : Fin 39)
  by_cases hk3 : k.val < 156
  · have hj : k.val - 117 < 39 := by omega
    have hn : (⟨117 + (k.val - 117), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 117 + (k.val - 117) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate3
      (⟨k.val - 117, hj⟩ : Fin 39)
  by_cases hk4 : k.val < 195
  · have hj : k.val - 156 < 39 := by omega
    have hn : (⟨156 + (k.val - 156), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 156 + (k.val - 156) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate4
      (⟨k.val - 156, hj⟩ : Fin 39)
  by_cases hk5 : k.val < 234
  · have hj : k.val - 195 < 39 := by omega
    have hn : (⟨195 + (k.val - 195), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 195 + (k.val - 195) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate5
      (⟨k.val - 195, hj⟩ : Fin 39)
  have hj : k.val - 234 < 39 := by omega
  have hn : (⟨234 + (k.val - 234), by omega⟩ : Fin 273) = k := by
    apply Fin.ext
    change 234 + (k.val - 234) = k.val
    omega
  simpa only [hn] using generatedSixth_middle_octad_phase_weight_certificate6
    (⟨k.val - 234, hj⟩ : Fin 39)

/-- Each displayed central phase is the genuine original preferred-short phase. -/
theorem generatedSixth_middle_octad_phase (k : Fin 273) :
    generatedSixthMiddleShortPhase (generatedSixthMiddleOctadInput k) =
      generatedSixthMiddleOctadPhase k := by
  exact (generatedSixth_pair_Q_phase (generatedSixthMiddleOctadInput k).1
    (generatedSixthMiddleOctadInput k).2).trans
      (generatedSixth_middle_octad_phase_weight_certificate k).1

/-- Every displayed actual octad coordinate has its exact signed numerator over four. -/
theorem generatedSixth_middle_octad_coefficient (k : Fin 273) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (generatedSixthMiddleOctadOutput k) =
      (generatedSixthMiddleOctadWeight k : ℝ) / 4 := by
  have h := generatedSixth_middle_short_coefficient (generatedSixthMiddleOctadInput k)
  rw [generatedSixth_middle_octad_permutation, generatedSixth_middle_octad_phase] at h
  have hw := (generatedSixth_middle_octad_phase_weight_certificate k).2
  by_cases hz : generatedSixthMiddleOctadPhase k = 0
  · rw [qSign, ite_eq_left hz, one_mul] at h
    rw [ite_eq_left hz] at hw
    rw [hw] at h
    exact h
  · rw [qSign, ite_eq_right hz, neg_one_mul] at h
    rw [ite_eq_right hz] at hw
    have hr : -(generatedSixthSourceShortWeight (generatedSixthMiddleOctadInput k) : ℝ) =
        (generatedSixthMiddleOctadWeight k : ℝ) := by exact_mod_cast hw
    rw [hr] at h
    exact h

/-- All displayed signed coefficient numerators are nonzero. -/
theorem generatedSixthMiddleOctadWeight_ne_zero (k : Fin 273) :
    generatedSixthMiddleOctadWeight k ≠ 0 := by
  revert k
  decide +kernel

/-- Every displayed actual octad target has nonzero original middle coefficient. -/
theorem generatedSixth_middle_octad_coefficient_ne_zero (k : Fin 273) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (generatedSixthMiddleOctadOutput k) ≠ 0 := by
  rw [generatedSixth_middle_octad_coefficient]
  apply div_ne_zero
  · exact_mod_cast generatedSixthMiddleOctadWeight_ne_zero k
  · norm_num

/-- Every octad coordinate outside the displayed actual 273 targets is zero. -/
theorem generatedSixth_middle_octad_zero (o : Fin 759) (e : Fin 64)
    (hr : ¬ ∃ k : Fin 273, generatedSixthMiddleOctadOutput k = Sum.inr (Sum.inl (o, e))) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inl (o, e))) = 0 := by
  apply generatedSixth_middle_short_zero
  rintro ⟨⟨s,p⟩, hp⟩
  obtain ⟨k, hk⟩ := generatedSixth_middle_octad_actual_source s p o e hp
  apply hr
  refine ⟨k, ?_⟩
  rw [← generatedSixth_middle_octad_permutation, hk]
  exact hp

/-- Every nonzero actual octad coordinate occurs in the genuine finite target list. -/
theorem generatedSixth_middle_octad_support_complete (o : Fin 759) (e : Fin 64)
    (h : (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inl (o, e))) ≠ 0) :
    ∃ k : Fin 273, generatedSixthMiddleOctadOutput k = Sum.inr (Sum.inl (o, e)) := by
  by_contra hr
  exact h (generatedSixth_middle_octad_zero o e hr)

/-- The genuine octad addresses with nonzero actual middle coefficient. -/
def generatedSixthMiddleOctadSupport :=
  {p : Fin 759 × Fin 64 //
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (Sum.inr (Sum.inl p)) ≠ 0}

/-- Each displayed actual target is an element of the genuine nonzero octad support. -/
def generatedSixthMiddleOctadSupportEntry (k : Fin 273) : generatedSixthMiddleOctadSupport :=
  ⟨generatedSixthMiddleOctadTargetCoordinates k,
    generatedSixth_middle_octad_coefficient_ne_zero k⟩

/-- The displayed 273 entries enumerate all genuine nonzero octad addresses exactly once. -/
theorem generatedSixthMiddleOctadSupportEntry_bijective :
    Function.Bijective generatedSixthMiddleOctadSupportEntry := by
  constructor
  · intro k l h
    apply generatedSixthMiddleOctadOutput_injective
    have he := congrArg (fun p : generatedSixthMiddleOctadSupport =>
      (Sum.inr (Sum.inl p.val) : GriessShortIndex)) h
    exact he
  · rintro ⟨⟨o, e⟩, h⟩
    obtain ⟨k, hk⟩ := generatedSixth_middle_octad_support_complete o e h
    refine ⟨k, Subtype.ext ?_⟩
    exact Sum.inl.inj (Sum.inr.inj hk)

/-- Exactly 273 actual octad coordinates have nonzero original middle coefficient. -/
theorem generatedSixthMiddleOctadSupport_card :
    Nat.card generatedSixthMiddleOctadSupport = 273 := by
  rw [← Nat.card_congr (Equiv.ofBijective generatedSixthMiddleOctadSupportEntry
    generatedSixthMiddleOctadSupportEntry_bijective)]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
