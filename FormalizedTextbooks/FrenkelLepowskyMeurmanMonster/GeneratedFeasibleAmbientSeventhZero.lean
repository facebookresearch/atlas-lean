/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadFourierArithmetic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOctadFamilies
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalog

/-! The Seventh local family: exactly three actual signed-short axes are orthogonal to the
actual Seventh prototype.

The canonical Seventh axis differs from the prototype by an actual element of Q, which fixes
the matrix block. The matrix numerator over 32 dominates `5 I`, so orthogonality needs a
short numerator of absolute value at least five. Odd numerators and all octad families but
one have absolute value at most three; the remaining family and the 1104 pair addresses
are checked with exact integer arithmetic. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem matrix_inclQ (q : Q) (x : GriessSpace) :
    (griessConwayEncode (rhoLocal (inclQ q) x)).1 = (griessConwayEncode x).1 := by
  change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).1 = _
  rw [localGriessRepresentation_encode]
  change conwayMatrixAction (1 : leechIsomSubgroup) (griessConwayEncode x).1 = _
  rw [map_one]
  rfl

/-- The three exceptional coordinate pairs of the Seventh matrix. -/
def generatedFeasibleAmbientSeventhTarget (a b : Fin 24) : ℤ :=
  if (a = 16 ∧ b = 17) ∨ (a = 16 ∧ b = 19) ∨ (a = 17 ∧ b = 19) then 1 else 0

/-- Diagonal numerators of the Seventh matrix, over 32. -/
def generatedFeasibleAmbientSeventhDiag (i : Fin 24) : ℤ :=
  if i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 18 then 17 else 9

/-- The matrix numerator, over 32, of the actual Seventh prototype. -/
def generatedFeasibleAmbientSeventhN (i j : Fin 24) : ℤ :=
  if i = j then generatedFeasibleAmbientSeventhDiag i
  else 4 * generatedFeasibleAmbientSeventhTarget (if i < j then i else j) (if i < j then j else i)

private theorem seventh_axis_matrix (i j : Fin 24) :
    (griessConwayEncode generatedSeventhAxis).1 i j =
      (generatedFeasibleAmbientSeventhN i j : ℝ) / 32 := by
  rw [generatedSeventh_axis_matrix]
  have hv (a b : Fin 24) : generatedSeventhMiddlePairValue 0 a b =
      (generatedFeasibleAmbientSeventhTarget a b : ℝ) / 4 := by
    unfold generatedSeventhMiddlePairValue generatedFeasibleAmbientSeventhTarget
    simp only [ite_true]
    split_ifs <;> norm_num
  unfold generatedSeventhAxisMatrix generatedFeasibleAmbientSeventhN
    generatedFeasibleAmbientSeventhDiag
  rw [hv]
  split_ifs <;> push_cast <;> ring

/-- Every actual matrix coordinate of the canonical Seventh axis. -/
theorem generatedFeasibleAmbient_seventh_matrix (i j : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).1 i j =
      (generatedFeasibleAmbientSeventhN i j : ℝ) / 32 := by
  obtain ⟨q, _, hq⟩ := generatedSeventhXi_canonical_axis_correction
  rw [← seventh_axis_matrix, hq, matrix_inclQ]

/-- Rank-one directions of the positive semidefinite certificate. -/
def generatedFeasibleAmbientSeventhW (k i : Fin 24) : ℤ :=
  if k = 16 then (if i = 16 ∨ i = 17 ∨ i = 19 then 1 else 0)
  else if i = k then 1 else 0

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientSeventhC (k : Fin 24) : ℤ :=
  if k = 16 then 4 else if k = 17 ∨ k = 19 then 0 else generatedFeasibleAmbientSeventhDiag k - 5

private theorem decomp : ∀ i j : Fin 24, 1 * generatedFeasibleAmbientSeventhN i j =
    1 * 5 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientSeventhC k *
      (generatedFeasibleAmbientSeventhW k i * generatedFeasibleAmbientSeventhW k j) := by
  unfold generatedFeasibleAmbientSeventhN generatedFeasibleAmbientSeventhC
    generatedFeasibleAmbientSeventhW generatedFeasibleAmbientSeventhDiag
    generatedFeasibleAmbientSeventhTarget
  decide +kernel

private theorem seventh_quad_ge (r : GriessShortIndex) :
    160 ≤ generatedFeasibleAmbientQuad generatedFeasibleAmbientSeventhN
      (griessShortIntegral r) := by
  have h := generatedFeasibleAmbient_quad_ge_of_decomp _ 5 1 generatedFeasibleAmbientSeventhC
    generatedFeasibleAmbientSeventhW (by norm_num)
    (by
      intro k
      unfold generatedFeasibleAmbientSeventhC generatedFeasibleAmbientSeventhDiag
      split_ifs <;> norm_num) decomp (griessShortIntegral r)
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  rw [hs] at h
  linarith

/-- The short numerators, over 32, of the canonical Seventh axis. -/
def generatedFeasibleAmbientSeventhShort : GriessShortIndex → ℤ
  | Sum.inl (s, p) =>
      4 * generatedFeasibleAmbientSeventhTarget (generatedAxisGlobalPairCoordinates p).1
          (generatedAxisGlobalPairCoordinates p).2 +
        (if s = 0 then 1 else -1) *
          generatedSeventhNormEightVectorData 7 (generatedAxisGlobalPairCoordinates p).1 *
          generatedSeventhNormEightVectorData 7 (generatedAxisGlobalPairCoordinates p).2
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ g : Fin 231, generatedSeventhXiOctadFourierNumerator g e *
        (if generatedSeventhXiOctadCodes g = (generatedAxisGlobalOctadCodeData o).val then 1
          else 0)
  | Sum.inr (Sum.inr (d, i)) =>
      -nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        generatedSeventhFrameVectorData 7 0 i *
        (generatedSeventhXiPlaneSpinInteger ⟨d.val, by omega⟩ +
          generatedSeventhXiPlaneSpinInteger ⟨d.val + 2048, by omega⟩)

private theorem canonical_middle_pair (t : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1 (Sum.inl (t, p)) =
      generatedSeventhMiddlePairValue t (griessCoordinatePair p).1
        (griessCoordinatePair p).2 := by
  rw [generatedSeventhXiPlaneCanonicalMiddle_encode]
  exact generatedSeventh_middle_pair_coordinate t p

/-- Every actual short coordinate of the canonical Seventh axis. -/
theorem generatedFeasibleAmbient_seventh_short (r : GriessShortIndex) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1 r =
      (generatedFeasibleAmbientSeventhShort r : ℝ) / 32 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rw [generatedSeventhXiPlaneCanonicalAxis, generatedSeventhXi_pair_triality_coordinate,
      canonical_middle_pair, canonical_middle_pair, generatedSeventhXi_canonical_middle_matrix]
    have hn := griessCoordinatePair_ne p
    have h0 (a b : Fin 24) : generatedSeventhMiddlePairValue 0 a b =
        (generatedFeasibleAmbientSeventhTarget a b : ℝ) / 4 := by
      unfold generatedSeventhMiddlePairValue generatedFeasibleAmbientSeventhTarget
      simp only [ite_true]
      split_ifs <;> norm_num
    have h1 (a b : Fin 24) : generatedSeventhMiddlePairValue 1 a b = 0 := by
      simp [generatedSeventhMiddlePairValue]
    simp only [hn, ite_false, zero_add, generatedFeasibleAmbientSeventhShort,
      generatedAxisGlobalPairCoordinates_actual, h0, h1]
    split_ifs <;> push_cast <;> ring
  · rw [generatedSeventhXi_canonical_octad_fourier]
    simp only [generatedFeasibleAmbientSeventhShort, generatedAxisGlobalOctadCodeData_actual]
  · rw [generatedSeventhXi_canonical_axis_odd]
    simp only [generatedFeasibleAmbientSeventhShort, Int.cast_mul, Int.cast_neg,
      Int.cast_add, nortonUIntegerSign_real]

private theorem seventh_zero_iff (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedSeventhXiPlaneCanonicalAxis = 0 ↔
      generatedFeasibleAmbientQuad generatedFeasibleAmbientSeventhN (griessShortIntegral r) =
        32 * generatedFeasibleAmbientSign c * generatedFeasibleAmbientSeventhShort r := by
  rw [generatedFeasibleAmbient_axis_form_eq_zero_iff_int r c generatedSeventhXiPlaneCanonicalAxis
    generatedFeasibleAmbientSeventhN (generatedFeasibleAmbientSeventhShort r) 32 32
    (by norm_num) (by norm_num) generatedFeasibleAmbient_seventh_matrix
    (generatedFeasibleAmbient_seventh_short r)]
  unfold generatedFeasibleAmbientQuad generatedFeasibleAmbientSign
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

private theorem seventh_ne_of_small (r : GriessShortIndex) (c : ZMod 2)
    (hn : |generatedFeasibleAmbientSeventhShort r| ≤ 4) :
    griessForm (conwayShortAxis r c) generatedSeventhXiPlaneCanonicalAxis ≠ 0 := by
  rw [Ne, seventh_zero_iff]
  intro h
  have hq := seventh_quad_ge r
  rw [h] at hq
  have hb := abs_le.mp hn
  unfold generatedFeasibleAmbientSign at hq
  split_ifs at hq <;> linarith [hb.1, hb.2]

private theorem frame_abs : ∀ i : Fin 24, |generatedSeventhFrameVectorData 7 0 i| ≤ 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
-- All 2048 paired spin addresses are checked.
private theorem spin_sum_abs : ∀ d : Fin 2048,
    |generatedSeventhXiPlaneSpinInteger ⟨d.val, by omega⟩ +
      generatedSeventhXiPlaneSpinInteger ⟨d.val + 2048, by omega⟩| ≤ 1 := by
  unfold generatedSeventhXiPlaneSpinInteger
  decide +kernel

private theorem odd_short_abs (d : Fin 2048) (i : Fin 24) :
    |generatedFeasibleAmbientSeventhShort (Sum.inr (Sum.inr (d, i)))| ≤ 3 := by
  simp only [generatedFeasibleAmbientSeventhShort]
  have hs (c : ZMod 2) : |nortonUIntegerSign c| = 1 := by
    unfold nortonUIntegerSign
    split_ifs <;> simp
  rw [abs_mul, abs_mul, abs_neg, hs, one_mul]
  calc _ ≤ 3 * 1 := mul_le_mul (frame_abs i) (spin_sum_abs d) (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

set_option maxRecDepth 100000 in
-- All 4096 actual octad Fourier entries are checked.
private theorem triality_entry_abs : ∀ e f : Fin 64, |trialityIntegerMatrix e f| = 1 := by
  unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
  decide +kernel

set_option maxRecDepth 100000 in
-- The 231 family codes are pairwise distinct.
private theorem codes_injective : ∀ g g' : Fin 231,
    generatedSeventhXiOctadCodes g = generatedSeventhXiOctadCodes g' → g = g' := by
  decide +kernel

set_option maxRecDepth 100000 in
-- Every family other than the distinguished one has three units of total weight.
private theorem weight_sum : ∀ g : Fin 231, g ≠ 2 →
    ∑ k : Fin 3, |generatedSeventhXiOctadWeights g k| ≤ 3 := by
  decide +kernel

private theorem fourier_abs (g : Fin 231) (e : Fin 64) (hg : g ≠ 2) :
    |generatedSeventhXiOctadFourierNumerator g e| ≤ 3 := by
  unfold generatedSeventhXiOctadFourierNumerator
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) (weight_sum g hg))
  apply Finset.sum_congr rfl
  intro k _
  rw [abs_mul, triality_entry_abs, mul_one]

/-- The integral short vector of the distinguished family, from its displayed data. -/
private def familyIntegral (e : Fin 64) (i : Fin 24) : ℤ :=
  if (golayEncodedMask (generatedSeventhXiOctadCode 2).val).testBit i.val then
    if (generatedSeventhXiOctadNegativeMask 2 e).testBit i.val then -2 else 2
  else 0

private theorem family_integral (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (generatedSeventhXiOctadFamily 2, e))) =
      familyIntegral e := by
  funext i
  simp only [griessShortIntegral, generatedSeventhXiOctadFamily_code,
    generatedSeventhXiOctadNegativeMask_actual, familyIntegral]

set_option maxRecDepth 100000 in
-- All 128 addresses of the distinguished family are checked exactly.
private theorem family_check : ∀ e : Fin 64, ∀ c : ZMod 2,
    generatedFeasibleAmbientQuad generatedFeasibleAmbientSeventhN (familyIntegral e) ≠
      32 * generatedFeasibleAmbientSign c * generatedSeventhXiOctadFourierNumerator 2 e := by
  unfold generatedFeasibleAmbientQuad generatedFeasibleAmbientSeventhN familyIntegral
    generatedFeasibleAmbientSeventhDiag generatedFeasibleAmbientSeventhTarget
    generatedFeasibleAmbientSign generatedSeventhXiOctadFourierNumerator
    generatedSeventhXiOctadNegativeMask generatedSeventhXiOctadCode
  decide +kernel

/-- No actual octad address is orthogonal to the canonical Seventh axis. -/
private theorem seventh_octad_ne (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)
      generatedSeventhXiPlaneCanonicalAxis ≠ 0 := by
  have hcode : (generatedAxisGlobalOctadCodeData o).val = (golayOctadLabel o).val := by
    rw [generatedAxisGlobalOctadCodeData_actual]
  by_cases hg : ∃ g : Fin 231, generatedSeventhXiOctadCodes g = (golayOctadLabel o).val
  · obtain ⟨g, hg⟩ := hg
    have hsum : generatedFeasibleAmbientSeventhShort (Sum.inr (Sum.inl (o, e))) =
        generatedSeventhXiOctadFourierNumerator g e := by
      simp only [generatedFeasibleAmbientSeventhShort, hcode]
      rw [Finset.sum_eq_single g]
      · simp [hg]
      · intro g' _ hne
        have : generatedSeventhXiOctadCodes g' ≠ (golayOctadLabel o).val := by
          intro h'
          exact hne (codes_injective g' g (h'.trans hg.symm))
        simp [this]
      · simp
    by_cases h2 : g = 2
    · subst h2
      have ho : o = generatedSeventhXiOctadFamily 2 := by
        apply golayOctadLabel_injective
        apply Fin.ext
        rw [generatedSeventhXiOctadFamily_code, ← hg]
        rfl
      subst ho
      rw [Ne, seventh_zero_iff, family_integral, hsum]
      exact family_check e c
    · apply seventh_ne_of_small
      rw [hsum]
      exact (fourier_abs g e h2).trans (by norm_num)
  · apply seventh_ne_of_small
    have hz : generatedFeasibleAmbientSeventhShort (Sum.inr (Sum.inl (o, e))) = 0 := by
      simp only [generatedFeasibleAmbientSeventhShort, hcode]
      apply Finset.sum_eq_zero
      intro g _
      have : generatedSeventhXiOctadCodes g ≠ (golayOctadLabel o).val := fun h => hg ⟨g, h⟩
      simp [this]
    rw [hz]
    norm_num

private theorem quad_diag (u d : Fin 24 → ℤ) :
    ∑ i, ∑ j, u i * (if i = j then d i else 0) * u j = ∑ i, d i * u i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem quad_entry (u : Fin 24 → ℤ) (a b : Fin 24) (x : ℤ) :
    ∑ i, ∑ j, u i * (if i = a ∧ j = b then x else 0) * u j = x * (u a * u b) := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp only [and_self, ite_true]
      ring
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hi]
  · simp

private theorem seventhN_split : ∀ i j : Fin 24, generatedFeasibleAmbientSeventhN i j =
    (if i = j then generatedFeasibleAmbientSeventhDiag i else 0) +
      (if i = 16 ∧ j = 17 then 4 else 0) + (if i = 17 ∧ j = 16 then 4 else 0) +
      (if i = 16 ∧ j = 19 then 4 else 0) + (if i = 19 ∧ j = 16 then 4 else 0) +
      (if i = 17 ∧ j = 19 then 4 else 0) + (if i = 19 ∧ j = 17 then 4 else 0) := by
  unfold generatedFeasibleAmbientSeventhN generatedFeasibleAmbientSeventhDiag
    generatedFeasibleAmbientSeventhTarget
  decide +kernel

/-- The Seventh quadratic form in closed sparse form. -/
private theorem seventh_quad (u : Fin 24 → ℤ) :
    generatedFeasibleAmbientQuad generatedFeasibleAmbientSeventhN u =
      ∑ i, generatedFeasibleAmbientSeventhDiag i * u i ^ 2 +
        8 * (u 16 * u 17 + u 16 * u 19 + u 17 * u 19) := by
  unfold generatedFeasibleAmbientQuad
  simp_rw [seventhN_split, mul_add, add_mul, Finset.sum_add_distrib]
  rw [quad_diag, quad_entry, quad_entry, quad_entry, quad_entry, quad_entry, quad_entry]
  ring

/-- The decidable pair condition, from the two pair coordinates. -/
private def pairZero (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Prop :=
  let u : Fin 24 → ℤ := fun i =>
    4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  (∑ i, generatedFeasibleAmbientSeventhDiag i * u i ^ 2 +
      8 * (u 16 * u 17 + u 16 * u 19 + u 17 * u 19)) =
    32 * generatedFeasibleAmbientSign c *
      (4 * generatedFeasibleAmbientSeventhTarget a b +
        (if s = 0 then 1 else -1) * generatedSeventhNormEightVectorData 7 a *
          generatedSeventhNormEightVectorData 7 b)

private instance (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Decidable (pairZero s a b c) := by
  unfold pairZero
  infer_instance

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedSeventhXiPlaneCanonicalAxis = 0 ↔
      pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c := by
  rw [seventh_zero_iff, seventh_quad]
  simp only [generatedFeasibleAmbientSeventhShort, generatedAxisGlobalPairCoordinates_actual]
  rfl

private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2)
        generatedSeventhXiPlaneCanonicalAxis = 0).card = 3 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 q.2 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  unfold pairZero generatedFeasibleAmbientSign generatedFeasibleAmbientSeventhDiag
    generatedFeasibleAmbientSeventhTarget
  decide +kernel

private theorem octad_card :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2)
        generatedSeventhXiPlaneCanonicalAxis = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact seventh_octad_ne q.1.1 q.1.2 q.2

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2)
        generatedSeventhXiPlaneCanonicalAxis = 0).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact seventh_ne_of_small _ q.2 ((odd_short_abs q.1.1 q.1.2).trans (by norm_num))

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) generatedSeventhXiPlaneCanonicalAxis = 0).card =
      3 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) generatedSeventhXiPlaneCanonicalAxis = 0)
  rw [pair_card, octad_card, odd_card] at h
  exact h

/-- Exactly three actual signed-short axes are orthogonal to the actual Seventh prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_seventh :
    generatedFeasibleAmbientAxisZeroCount generatedSeventhAxis = 3 := by
  obtain ⟨q, _, hq⟩ := generatedSeventhXi_canonical_axis_correction
  rw [hq]
  change generatedFeasibleAmbientAxisZeroCount
    ((inclQ q : H) • generatedSeventhXiPlaneCanonicalAxis) = 3
  rw [generatedFeasibleAmbientAxisZeroCount_smul, generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
