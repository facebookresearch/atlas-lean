/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientFourthData

/-! The Fourth local family: at most 63 actual signed-short axes are orthogonal to the actual
Fourth prototype.

The matrix numerator dominates `2 I`, so addresses with zero short coordinate are never
orthogonal; odd coordinates and octads outside the 63 listed families vanish. The 1104
pair addresses give exactly 31 orthogonal axes, and the listed octad families give at
most 32, all checked with exact integer arithmetic. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem fourthN_split : ∀ i j : Fin 24, generatedFeasibleAmbientFourthN i j =
    (if i = j then generatedFourthProjectionDiagonal i else 0) +
      (if i = 8 ∧ j = 11 then -8 else 0) + (if i = 11 ∧ j = 8 then -8 else 0) := by
  unfold generatedFeasibleAmbientFourthN generatedFourthProjectionDiagonal
  decide +kernel

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

/-- The Fourth quadratic form in closed sparse form. -/
private theorem fourth_quad (u : Fin 24 → ℤ) :
    generatedFeasibleAmbientQuad generatedFeasibleAmbientFourthN u =
      ∑ i, generatedFourthProjectionDiagonal i * u i ^ 2 - 16 * (u 8 * u 11) := by
  unfold generatedFeasibleAmbientQuad
  simp_rw [fourthN_split, mul_add, add_mul, Finset.sum_add_distrib]
  rw [quad_diag, quad_entry, quad_entry]
  ring

private theorem fourth_quad_pos (r : GriessShortIndex) :
    64 ≤ generatedFeasibleAmbientQuad generatedFeasibleAmbientFourthN (griessShortIntegral r) := by
  have h := generatedFeasibleAmbient_fourth_quad_ge (griessShortIntegral r)
  have hs := griessShortIntegral_squareSum r
  unfold leechSquareSum at hs
  rw [hs] at h
  linarith

private theorem fourth_zero_iff (r : GriessShortIndex) (c : ZMod 2) :
    griessForm (conwayShortAxis r c) generatedFourthAxis = 0 ↔
      generatedFeasibleAmbientQuad generatedFeasibleAmbientFourthN (griessShortIntegral r) =
        32 * generatedFeasibleAmbientSign c * generatedFeasibleAmbientFourthShort r := by
  rw [generatedFeasibleAmbient_axis_form_eq_zero_iff_int r c generatedFourthAxis
    generatedFeasibleAmbientFourthN (generatedFeasibleAmbientFourthShort r) 16 16
    (by norm_num) (by norm_num) generatedFeasibleAmbient_fourth_matrix
    (generatedFeasibleAmbient_fourth_short r)]
  unfold generatedFeasibleAmbientQuad generatedFeasibleAmbientSign
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

private theorem fourth_ne_of_zero (r : GriessShortIndex) (c : ZMod 2)
    (h0 : generatedFeasibleAmbientFourthShort r = 0) :
    griessForm (conwayShortAxis r c) generatedFourthAxis ≠ 0 := by
  rw [Ne, fourth_zero_iff, h0, mul_zero]
  have := fourth_quad_pos r
  omega

/-- The decidable pair condition, from the two pair coordinates. -/
private def pairZero (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Prop :=
  let u : Fin 24 → ℤ := fun i =>
    4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  (∑ i, generatedFourthProjectionDiagonal i * u i ^ 2 - 16 * (u 8 * u 11)) =
    32 * generatedFeasibleAmbientSign c * generatedFourthLiftShortPairNumerator s a b

private instance (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Decidable (pairZero s a b c) := by
  unfold pairZero
  infer_instance

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedFourthAxis = 0 ↔
      pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c := by
  rw [fourth_zero_iff, fourth_quad]
  simp only [generatedFeasibleAmbientFourthShort, generatedAxisGlobalPairCoordinates_actual]
  rfl

private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2) generatedFourthAxis = 0).card = 31 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 q.2 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  unfold pairZero generatedFeasibleAmbientSign generatedFourthLiftShortPairNumerator
    generatedFourthQShortBasisProjectionNumerator generatedFourthProjectionDiagonal
  decide +kernel

/-- The physical sign mask of a listed octad family, from its displayed coordinates. -/
private def familySignMask (j : Fin 63) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedFourthEvenRootCoordinates j k).val else 0) ||| m) 0

/-- The integral short vector of a listed octad family. -/
private def familyIntegral (j : Fin 63) (e : Fin 64) (i : Fin 24) : ℤ :=
  if (golayEncodedMask (generatedFourthEvenRootCode j).val).testBit i.val then
    if (familySignMask j e).testBit i.val then -2 else 2
  else 0

private theorem family_integral (j : Fin 63) (e : Fin 64) :
    griessShortIntegral (Sum.inr (Sum.inl (generatedFourthEvenRootOctad j, e))) =
      familyIntegral j e := by
  funext i
  simp only [griessShortIntegral, griessOctadSignMask, generatedFourthEvenRootOctad_label,
    generatedFourth_even_coordinates_certificate, familyIntegral, familySignMask]

/-- The listed canonical octad families and signs found by the finite check. -/
private def octadZeroList : Finset (Fin 63 × Fin 64 × ZMod 2) :=
  {(0, 0, 0), (0, 1, 0), (0, 2, 1), (0, 3, 0), (0, 4, 1), (0, 5, 0), (0, 6, 1), (0, 7, 1),
    (0, 8, 1), (0, 9, 0), (0, 10, 1), (0, 11, 1), (0, 12, 1), (0, 13, 1), (0, 14, 0), (0, 15, 1),
    (0, 32, 1), (0, 33, 0), (0, 34, 1), (0, 35, 1), (0, 36, 1), (0, 37, 1), (0, 38, 0),
    (0, 39, 1), (0, 40, 1), (0, 41, 1), (0, 42, 0), (0, 43, 1), (0, 44, 0), (0, 45, 1),
    (0, 46, 0), (0, 47, 0)}

set_option maxRecDepth 100000 in
-- The 32 listed entries are distinct.
private theorem octadZeroList_card : octadZeroList.card = 32 := by
  decide +kernel

/-- The first listed family with the same Golay code. -/
private def canon : Fin 63 → Fin 63 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 31, 33, 33, 35, 35, 37, 37, 39, 39, 41, 41, 43, 43, 45, 45, 47, 47,
    49, 49, 51, 51, 53, 53, 55, 55, 57, 57, 59, 59, 61, 61]

private def familyZero (j : Fin 63) (e : Fin 64) (c : ZMod 2) : Prop :=
  (∑ i, generatedFourthProjectionDiagonal i * familyIntegral j e i ^ 2 -
      16 * (familyIntegral j e 8 * familyIntegral j e 11)) =
    32 * generatedFeasibleAmbientSign c *
      (2 * generatedFourthQShortBasisOctadNumerator (generatedFourthEvenRootCode j) e)

private instance (j : Fin 63) (e : Fin 64) (c : ZMod 2) : Decidable (familyZero j e c) := by
  unfold familyZero
  infer_instance

set_option maxRecDepth 100000 in
-- One quarter of the 8064 listed family addresses, checked with exact integer arithmetic.
private theorem family_check_0 : ∀ jj : Fin 16, ∀ e : Fin 64, ∀ c : ZMod 2,
    if hj : 0 + jj.val < 63 then
      (familyZero ⟨0 + jj.val, hj⟩ e c → (canon ⟨0 + jj.val, hj⟩, e, c) ∈ octadZeroList)
    else True := by
  unfold familyZero familyIntegral familySignMask generatedFeasibleAmbientSign
    generatedFourthQShortBasisOctadNumerator generatedFourthProjectionDiagonal
  decide +kernel

set_option maxRecDepth 100000 in
-- One quarter of the 8064 listed family addresses, checked with exact integer arithmetic.
private theorem family_check_1 : ∀ jj : Fin 16, ∀ e : Fin 64, ∀ c : ZMod 2,
    if hj : 16 + jj.val < 63 then
      (familyZero ⟨16 + jj.val, hj⟩ e c → (canon ⟨16 + jj.val, hj⟩, e, c) ∈ octadZeroList)
    else True := by
  unfold familyZero familyIntegral familySignMask generatedFeasibleAmbientSign
    generatedFourthQShortBasisOctadNumerator generatedFourthProjectionDiagonal
  decide +kernel

set_option maxRecDepth 100000 in
-- One quarter of the 8064 listed family addresses, checked with exact integer arithmetic.
private theorem family_check_2 : ∀ jj : Fin 16, ∀ e : Fin 64, ∀ c : ZMod 2,
    if hj : 32 + jj.val < 63 then
      (familyZero ⟨32 + jj.val, hj⟩ e c → (canon ⟨32 + jj.val, hj⟩, e, c) ∈ octadZeroList)
    else True := by
  unfold familyZero familyIntegral familySignMask generatedFeasibleAmbientSign
    generatedFourthQShortBasisOctadNumerator generatedFourthProjectionDiagonal
  decide +kernel

set_option maxRecDepth 100000 in
-- One quarter of the 8064 listed family addresses, checked with exact integer arithmetic.
private theorem family_check_3 : ∀ jj : Fin 16, ∀ e : Fin 64, ∀ c : ZMod 2,
    if hj : 48 + jj.val < 63 then
      (familyZero ⟨48 + jj.val, hj⟩ e c → (canon ⟨48 + jj.val, hj⟩, e, c) ∈ octadZeroList)
    else True := by
  unfold familyZero familyIntegral familySignMask generatedFeasibleAmbientSign
    generatedFourthQShortBasisOctadNumerator generatedFourthProjectionDiagonal
  decide +kernel

private theorem family_check (j : Fin 63) (e : Fin 64) (c : ZMod 2) (h : familyZero j e c) :
    (canon j, e, c) ∈ octadZeroList := by
  have jj : j.val % 16 < 16 := Nat.mod_lt _ (by decide)
  rcases (show j.val / 16 = 0 ∨ j.val / 16 = 1 ∨ j.val / 16 = 2 ∨ j.val / 16 = 3 by omega)
    with hq | hq | hq | hq
  · have := family_check_0 ⟨j.val % 16, jj⟩ e c
    rw [dite_eq_left (show 0 + j.val % 16 < 63 by omega)] at this
    have he' : (⟨0 + j.val % 16, by omega⟩ : Fin 63) = j := by
      apply Fin.ext
      dsimp
      omega
    rw [he'] at this
    exact this h
  · have := family_check_1 ⟨j.val % 16, jj⟩ e c
    rw [dite_eq_left (show 16 + j.val % 16 < 63 by omega)] at this
    have he' : (⟨16 + j.val % 16, by omega⟩ : Fin 63) = j := by
      apply Fin.ext
      dsimp
      omega
    rw [he'] at this
    exact this h
  · have := family_check_2 ⟨j.val % 16, jj⟩ e c
    rw [dite_eq_left (show 32 + j.val % 16 < 63 by omega)] at this
    have he' : (⟨32 + j.val % 16, by omega⟩ : Fin 63) = j := by
      apply Fin.ext
      dsimp
      omega
    rw [he'] at this
    exact this h
  · have := family_check_3 ⟨j.val % 16, jj⟩ e c
    rw [dite_eq_left (show 48 + j.val % 16 < 63 by omega)] at this
    have he' : (⟨48 + j.val % 16, by omega⟩ : Fin 63) = j := by
      apply Fin.ext
      dsimp
      omega
    rw [he'] at this
    exact this h

private theorem canon_code : ∀ j : Fin 63,
    generatedFourthEvenRootCode (canon j) = generatedFourthEvenRootCode j := by
  decide +kernel

private theorem canon_octad (j : Fin 63) :
    generatedFourthEvenRootOctad (canon j) = generatedFourthEvenRootOctad j := by
  apply golayOctadLabel_injective
  rw [generatedFourthEvenRootOctad_label, generatedFourthEvenRootOctad_label, canon_code]

/-- Every orthogonal octad address lies in the image of the listed family catalogue. -/
private theorem octad_mem (o : Fin 759) (e : Fin 64) (c : ZMod 2)
    (h : griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) generatedFourthAxis = 0) :
    ((o, e), c) ∈ octadZeroList.image fun t : Fin 63 × Fin 64 × ZMod 2 =>
      ((generatedFourthEvenRootOctad t.1, t.2.1), t.2.2) := by
  by_cases ho : ∃ j : Fin 63, generatedFourthEvenRootOctad j = o
  · obtain ⟨j, rfl⟩ := ho
    rw [fourth_zero_iff, family_integral, fourth_quad] at h
    have hz : familyZero j e c := by
      unfold familyZero
      rw [h]
      simp only [generatedFeasibleAmbientFourthShort, generatedAxisGlobalOctadCodeData_actual,
        generatedFourthEvenRootOctad_label]
    refine Finset.mem_image.mpr ⟨(canon j, e, c), family_check j e c hz, ?_⟩
    rw [canon_octad]
  · exfalso
    have h0 : generatedFeasibleAmbientFourthShort (Sum.inr (Sum.inl (o, e))) = 0 := by
      have hS := generatedFeasibleAmbient_fourth_short (Sum.inr (Sum.inl (o, e)))
      rw [generatedFourthQShortBasis_octad_zero_outside o e ho] at hS
      have hS' : ((generatedFeasibleAmbientFourthShort (Sum.inr (Sum.inl (o, e))) : ℤ) : ℝ) =
          0 := by linarith
      exact_mod_cast hS'
    exact fourth_ne_of_zero _ c h0 h

set_option linter.constructorNameAsVariable false in
-- This syntax linter overflows its default stack on the literal finite image below.
private theorem octad_subset :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2) generatedFourthAxis = 0) ⊆
      octadZeroList.image fun t : Fin 63 × Fin 64 × ZMod 2 =>
        ((generatedFourthEvenRootOctad t.1, t.2.1), t.2.2) := by
  rintro ⟨⟨o, e⟩, c⟩ hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  exact octad_mem o e c hq

private theorem octad_card_le :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2) generatedFourthAxis = 0).card ≤
      32 :=
  ((Finset.card_le_card octad_subset).trans Finset.card_image_le).trans
    (le_of_eq octadZeroList_card)

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2) generatedFourthAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  apply fourth_ne_of_zero
  rfl

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card_le :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) generatedFourthAxis = 0).card ≤ 63 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) generatedFourthAxis = 0)
  rw [pair_card, odd_card] at h
  have ho := octad_card_le
  omega

/-- At most 63 actual signed-short axes are orthogonal to the actual Fourth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_fourth_le :
    generatedFeasibleAmbientAxisZeroCount generatedFourthAxis ≤ 63 := by
  rw [generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card_le

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
