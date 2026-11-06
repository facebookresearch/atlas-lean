/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCandidateShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCandidateOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthMatrixCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingShortCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! The Twelfth local family: no actual signed-short axis is orthogonal to the actual
Twelfth prototype.

The certified Twelfth candidate axis lies in the prototype's local orbit and differs from it
by an actual element of Q, so it has the prototype's matrix. Its short numerators over 128
are packed signed multiples of four of absolute value at most sixteen, so every short
coordinate is at most one eighth in absolute value. The matrix numerator over 256 dominates
`48 I`, so the matrix contraction against every actual short vector is at least three
quarters, and the pairing `2 q - 8 (±1) S` never vanishes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The matrix numerator, over 256, of the actual Twelfth prototype. -/
def generatedFeasibleAmbientTwelfthN : Fin 24 → Fin 24 → ℤ :=
  ![![80, 0, 16, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -16, 0, 0, 0, 0],
    ![0, 80, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 0, 0, 0],
    ![16, 16, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, 16, 0, 0, 0, 0, 0, 0],
    ![-16, 16, 0, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, -16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 16, -16, 0, 0, 0, 0],
    ![0, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, -16, -16, 0, 0, 0, 0],
    ![16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -16, 112, 0, 0, 0, 0, 0],
    ![-16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16, -16, 0, 112, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80]]

/-- Rank-one directions of the positive semidefinite certificate. -/
def generatedFeasibleAmbientTwelfthW : Fin 24 → Fin 24 → ℤ :=
  ![![2, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0],
    ![0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -1, -1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientTwelfthC : Fin 24 → ℤ :=
  ![24, 24, 16, 16, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 16, 16, 96, 96, 96, 96, 96,
    96]

set_option maxRecDepth 100000 in
-- The 576 matrix entries are checked against 24 rank-one terms.
private theorem decomp : ∀ i j : Fin 24, 3 * generatedFeasibleAmbientTwelfthN i j =
    3 * 48 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientTwelfthC k *
      (generatedFeasibleAmbientTwelfthW k i * generatedFeasibleAmbientTwelfthW k j) := by
  decide +kernel

private theorem quad_ge (r : GriessShortIndex) :
    1536 ≤ generatedFeasibleAmbientQuad generatedFeasibleAmbientTwelfthN
      (griessShortIntegral r) := by
  have h := generatedFeasibleAmbient_quad_ge_of_decomp _ 48 3 generatedFeasibleAmbientTwelfthC
    generatedFeasibleAmbientTwelfthW (by norm_num) (by decide) decomp (griessShortIntegral r)
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  rw [hs] at h
  linarith

set_option maxRecDepth 100000 in
-- The 24 diagonal entries are the exact rational incoming diagonal.
private theorem diag_check : ∀ i : Fin 24,
    ((generatedFeasibleAmbientTwelfthN i i : ℤ) : ℚ) =
      256 * generatedTwelfthIncomingMatrixQ i i := by
  unfold generatedTwelfthIncomingMatrixQ generatedTwelfthStartingDiagonalQ
  decide +kernel

set_option maxRecDepth 100000 in
-- All 276 incoming pair coefficients are looked up in the existing exact cache.
private theorem pair_check : ∀ p : Fin 276,
    generatedFeasibleAmbientTwelfthN (generatedAxisGlobalPairCoordinates p).1
      (generatedAxisGlobalPairCoordinates p).2 =
      8 * (generatedTwelfthIncomingShortCoefficient (Sum.inl (0, p)) +
        generatedTwelfthIncomingShortCoefficient (Sum.inl (1, p))) := by
  decide +kernel

private theorem symm_check : ∀ i j : Fin 24,
    generatedFeasibleAmbientTwelfthN i j = generatedFeasibleAmbientTwelfthN j i := by
  decide +kernel

private theorem pairIndex_coordinates (i j : Fin 24) (h : i ≠ j) :
    griessCoordinatePair (griessPairIndex i j h) = if i < j then (i, j) else (j, i) := by
  simp only [griessCoordinatePair, griessPairIndex, Equiv.apply_symm_apply]

private theorem matrix_inclQ (q : Q) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (inclQ q) x)).1 = (griessConwayEncode x).1 := by
  change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).1 = _
  rw [localGriessRepresentation_encode]
  change conwayMatrixAction (1 : leechIsomSubgroup) (griessConwayEncode x).1 = _
  rw [map_one]
  rfl

/-- Every actual matrix coordinate of the actual Twelfth prototype. -/
theorem generatedFeasibleAmbient_twelfth_matrix (i j : Fin 24) :
    (griessConwayEncode generatedTwelfthAxis).1 i j =
      (generatedFeasibleAmbientTwelfthN i j : ℝ) / 256 := by
  rw [generatedTwelfth_matrix, generatedTwelfthPacket]
  change generatedAxisGlobalRawTrialityMatrix generatedAxisGlobalFifthRoot09Packet i j = _
  unfold generatedAxisGlobalRawTrialityMatrix
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl, ← generatedAxisGlobalFifthRoot09Packet_actual]
    change (griessConwayEncode (rhoLocal generatedTwelfthLocal generatedFifthAxis)).1 i i = _
    rw [generatedTwelfth_incoming_matrix_coordinate]
    have hd := diag_check i
    have hd' : ((generatedTwelfthIncomingMatrixQ i i : ℚ) : ℝ) =
        ((generatedFeasibleAmbientTwelfthN i i : ℚ) : ℝ) / 256 := by
      rw [hd]
      push_cast
      ring
    rw [hd']
    push_cast
    rfl
  · rw [dite_eq_right h, generatedTwelfth_incoming_short_actual,
      generatedTwelfth_incoming_short_actual]
    set p := griessPairIndex i j h with hp
    have hc := pairIndex_coordinates i j h
    rw [← hp, ← generatedAxisGlobalPairCoordinates_actual] at hc
    have hpair := pair_check p
    rw [hc] at hpair
    have hN : generatedFeasibleAmbientTwelfthN i j =
        8 * (generatedTwelfthIncomingShortCoefficient (Sum.inl (0, p)) +
          generatedTwelfthIncomingShortCoefficient (Sum.inl (1, p))) := by
      split_ifs at hpair with hij
      · exact hpair
      · rw [symm_check]
        exact hpair
    rw [hN]
    push_cast
    ring

/-- Every short numerator of the candidate axis has absolute value at most sixteen. -/
private theorem candidate_numerator_abs (r : GriessShortIndex) :
    |generatedTwelfthCompleteShortInputInteger r| ≤ 16 := by
  unfold generatedTwelfthCompleteShortInputInteger
  simp only
  generalize (generatedNinthLowerSpinShortWord generatedTwelfthCompleteShortInputWords
    (generatedNinthLowerSpinShortAddress r) /
      2 ^ (3 * ((generatedNinthLowerSpinShortAddress r).val % 16))) = w
  have hp : w % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize w % 8 = p at hp ⊢
  split_ifs with h <;> rw [abs_le] <;> constructor <;> omega

/-- Every short coordinate of the candidate axis has absolute value at most one eighth. -/
private theorem candidate_short_abs (r : GriessShortIndex) :
    |(griessConwayEncode generatedTwelfthIncomingCandidateAxis).2.1 r| ≤ 1 / 8 := by
  have h := generatedTwelfth_candidate_short_source_actual r
  have hn := candidate_numerator_abs r
  have hn' : |(generatedTwelfthCompleteShortInputInteger r : ℝ)| ≤ 16 := by exact_mod_cast hn
  rw [← h, abs_mul, show |(128 : ℝ)| = 128 by norm_num] at hn'
  linarith

private theorem candidate_matrix (i j : Fin 24) :
    (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 i j =
      (generatedFeasibleAmbientTwelfthN i j : ℝ) / 256 := by
  obtain ⟨h, hh, hax⟩ := generatedTwelfth_incoming_candidate_local_orbit
  have hr : h ∈ inclQ.range := by
    rw [inclQ_range_eq_projH_ker]
    exact hh
  obtain ⟨q, rfl⟩ := hr
  rw [← generatedFeasibleAmbient_twelfth_matrix, hax, matrix_inclQ]

private theorem contraction_ge (r : GriessShortIndex) :
    3 / 4 ≤ axisMatrixContraction (griessShortVector r)
      (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 := by
  have hc : axisMatrixContraction (griessShortVector r)
      (griessConwayEncode generatedTwelfthIncomingCandidateAxis).1 =
      (generatedFeasibleAmbientQuad generatedFeasibleAmbientTwelfthN
        (griessShortIntegral r) : ℝ) / 2048 := by
    unfold axisMatrixContraction generatedFeasibleAmbientQuad
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [candidate_matrix]
    calc griessShortVector r i * ((generatedFeasibleAmbientTwelfthN i j : ℝ) / 256) *
          griessShortVector r j
        = (generatedFeasibleAmbientTwelfthN i j : ℝ) / 256 *
          (griessShortVector r i * griessShortVector r j) := by ring
      _ = (generatedFeasibleAmbientTwelfthN i j : ℝ) / 256 *
          ((griessShortIntegral r i : ℝ) * griessShortIntegral r j / 8) := by
          rw [generatedFeasibleAmbient_shortVector_mul]
      _ = _ := by ring
  rw [hc, le_div_iff₀ (by norm_num : (0 : ℝ) < 2048)]
  have h := quad_ge r
  have h' : ((1536 : ℤ) : ℝ) ≤ (generatedFeasibleAmbientQuad generatedFeasibleAmbientTwelfthN
      (griessShortIntegral r) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- No actual signed-short axis is orthogonal to the certified Twelfth candidate axis. -/
theorem generatedFeasibleAmbient_twelfth_candidate_form_ne (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedTwelfthIncomingCandidateAxis ≠ 0 := by
  rw [generatedFeasibleAmbient_axis_form]
  have hq := contraction_ge r
  have hs := abs_le.mp (candidate_short_abs r)
  have hc : qSign c = 1 ∨ qSign c = -1 := by
    unfold qSign
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with hc | hc <;> rw [hc] <;> intro h <;> linarith [hs.1, hs.2]

/-- No actual signed-short axis is orthogonal to the actual Twelfth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_twelfth :
    generatedFeasibleAmbientAxisZeroCount generatedTwelfthAxis = 0 := by
  obtain ⟨h, _, hax⟩ := generatedTwelfth_incoming_candidate_local_orbit
  rw [hax]
  change generatedFeasibleAmbientAxisZeroCount (h • generatedTwelfthIncomingCandidateAxis) = 0
  rw [generatedFeasibleAmbientAxisZeroCount_smul]
  unfold generatedFeasibleAmbientAxisZeroCount
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨⟨r, c⟩, hrc⟩
  exact generatedFeasibleAmbient_twelfth_candidate_form_ne r c hrc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
