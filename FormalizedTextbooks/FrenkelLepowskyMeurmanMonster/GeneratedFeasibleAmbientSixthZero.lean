/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrix

/-! The Sixth local family: exactly one actual signed-short axis is orthogonal to the
actual Sixth prototype.

The matrix numerator of the prototype is `9 I + 2 v vᵀ + 6 w wᵀ`, so its quadratic form is
at least `9 · 32` on every actual short vector. Orthogonality needs a short numerator of
absolute value at least nine; every octad and odd numerator has absolute value at most
five, and the 1104 pair addresses are checked exactly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Integer matrix numerators of the actual Sixth prototype, over 32. -/
def generatedFeasibleAmbientSixthN (i j : Fin 24) : ℤ :=
  if i = j then (if i = 19 then 33 else if i = 16 ∨ i = 17 then 17 else 9)
  else 4 * generatedSixthMiddlePairNumerator 0 (if i < j then i else j) (if i < j then j else i)

/-- The actual matrix coordinates of the Sixth prototype. -/
theorem generatedFeasibleAmbient_sixth_matrix (i j : Fin 24) :
    (griessConwayEncode generatedSixthAxis).1 i j =
      (generatedFeasibleAmbientSixthN i j : ℝ) / 32 := by
  rw [generatedSixth_axis_matrix]
  unfold generatedSixthAxisMatrix generatedFeasibleAmbientSixthN generatedSixthMiddlePairValue
    generatedSixthMiddlePairNumerator
  split_ifs <;> norm_num

private def sixthV (i : Fin 24) : ℤ := if i = 16 then 1 else if i = 17 then -1 else 0

private def sixthW (i : Fin 24) : ℤ :=
  if i = 16 then 1 else if i = 17 then 1 else if i = 19 then -2 else 0

private theorem sixthN_decomp : ∀ i j : Fin 24, generatedFeasibleAmbientSixthN i j =
    9 * (if i = j then 1 else 0) + 2 * (sixthV i * sixthV j) + 6 * (sixthW i * sixthW j) := by
  unfold generatedFeasibleAmbientSixthN generatedSixthMiddlePairNumerator sixthV sixthW
  decide

/-- The Sixth quadratic form is `9 |u|² + 2 (v·u)² + 6 (w·u)²`. -/
private theorem sixth_quad (u : Fin 24 → ℤ) :
    ∑ i, ∑ j, u i * generatedFeasibleAmbientSixthN i j * u j =
      9 * ∑ i, u i ^ 2 + 2 * (∑ i, sixthV i * u i) ^ 2 + 6 * (∑ i, sixthW i * u i) ^ 2 := by
  have e1 : ∑ i, ∑ j, u i * generatedFeasibleAmbientSixthN i j * u j =
      ∑ i, ∑ j, 9 * (if i = j then u i * u j else 0) +
        ∑ i, ∑ j, 2 * ((sixthV i * u i) * (sixthV j * u j)) +
        ∑ i, ∑ j, 6 * ((sixthW i * u i) * (sixthW j * u j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [sixthN_decomp]
    split_ifs <;> ring
  have e2 : ∑ i, ∑ j, 9 * (if i = j then u i * u j else 0) = 9 * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, Finset.sum_ite_eq]
    simp [sq]
  have e3 (a : Fin 24 → ℤ) (k : ℤ) :
      ∑ i, ∑ j, k * (a i * a j) = k * (∑ i, a i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [e1, e2, e3, e3]

/-- Every actual short vector has Sixth quadratic value at least 288. -/
private theorem sixth_quad_ge (r : GriessShortIndex) :
    288 ≤ ∑ i, ∑ j, griessShortIntegral r i * generatedFeasibleAmbientSixthN i j *
      griessShortIntegral r j := by
  rw [sixth_quad]
  have h := griessShortIntegral_squareSum r
  unfold leechSquareSum at h
  rw [h]
  nlinarith [sq_nonneg (∑ i, sixthV i * griessShortIntegral r i),
    sq_nonneg (∑ i, sixthW i * griessShortIntegral r i)]

/-- Orthogonality at a short label in terms of its integer short numerator. -/
private theorem sixth_zero_iff (r : GriessShortIndex) (c : ZMod 2) (n : ℤ)
    (hS : (griessConwayEncode generatedSixthAxis).2.1 r = (n : ℝ) / 32) :
    griessForm (conwayShortAxis r c) generatedSixthAxis = 0 ↔
      (∑ i, ∑ j, griessShortIntegral r i * generatedFeasibleAmbientSixthN i j *
        griessShortIntegral r j) = 32 * (if c = 0 then 1 else -1) * n := by
  rw [generatedFeasibleAmbient_axis_form_eq_zero_iff_int r c generatedSixthAxis
    generatedFeasibleAmbientSixthN n 32 32 (by norm_num) (by norm_num)
    generatedFeasibleAmbient_sixth_matrix hS]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

/-- A short numerator of absolute value at most five never gives orthogonality. -/
private theorem sixth_ne_of_small (r : GriessShortIndex) (c : ZMod 2) (n : ℤ)
    (hS : (griessConwayEncode generatedSixthAxis).2.1 r = (n : ℝ) / 32) (hn : |n| ≤ 5) :
    griessForm (conwayShortAxis r c) generatedSixthAxis ≠ 0 := by
  rw [Ne, sixth_zero_iff r c n hS]
  intro h
  have hq := sixth_quad_ge r
  rw [h] at hq
  have hb := abs_le.mp hn
  split_ifs at hq <;> linarith [hb.1, hb.2]

set_option maxRecDepth 100000 in
-- All 4096 actual octad Fourier entries are checked.
private theorem triality_entry_abs : ∀ e f : Fin 64, |trialityIntegerMatrix e f| = 1 := by
  unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
  decide +kernel

set_option maxRecDepth 100000 in
-- All 231 cached octad families are checked.
private theorem cache_weight_sum : ∀ f : Fin 231,
    ∑ j ∈ generatedSixthFinalOctadCacheRows f, |generatedSixthMiddleOctadWeight j| ≤ 5 := by
  decide +kernel

private theorem cached_numerator_abs (f : Fin 231) (e : Fin 64) :
    |generatedSixthFinalOctadCachedNumerator f e| ≤ 5 := by
  unfold generatedSixthFinalOctadCachedNumerator
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) (cache_weight_sum f))
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul, triality_entry_abs, one_mul]

/-- No actual octad address is orthogonal to the Sixth prototype. -/
private theorem sixth_octad_ne (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) generatedSixthAxis ≠ 0 := by
  by_cases ho : ∃ f : Fin 231, generatedSixthFinalOctadCacheOctad f = o
  · obtain ⟨f, rfl⟩ := ho
    exact sixth_ne_of_small _ c _ (generatedSixth_final_octad_cached_coordinate f e)
      (cached_numerator_abs f e)
  · exact sixth_ne_of_small _ c 0
      (by rw [generatedSixth_final_octad_cached_zero o e ho]; simp) (by simp)

private theorem frame_abs : ∀ j : Fin 24, |generatedSixthFrameVectorData 8 0 j| ≤ 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
-- All 2048 paired spin addresses are checked.
private theorem phase_sum_abs : ∀ d : Fin 2048,
    |generatedSixthPackedSpinPhase ⟨d.val, by omega⟩ +
      generatedSixthPackedSpinPhase ⟨d.val + 2048, by omega⟩| ≤ 1 := by
  unfold generatedSixthPackedSpinPhase
  decide +kernel

private theorem odd_numerator_abs (d : Fin 2048) (j : Fin 24) :
    |generatedSixthFinalOddNumerator d j| ≤ 5 := by
  unfold generatedSixthFinalOddNumerator
  have hs (c : ZMod 2) : |nortonUIntegerSign c| = 1 := by
    unfold nortonUIntegerSign
    split_ifs <;> simp
  rw [abs_mul, abs_mul, abs_neg, hs, one_mul]
  have h1 := frame_abs j
  have h2 := phase_sum_abs d
  calc _ ≤ 5 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 5 := by norm_num

/-- No actual odd address is orthogonal to the Sixth prototype. -/
private theorem sixth_odd_ne (d : Fin 2048) (j : Fin 24) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inr (d, j))) c) generatedSixthAxis ≠ 0 :=
  sixth_ne_of_small _ c _ (generatedSixth_final_odd_coordinate d j) (odd_numerator_abs d j)

/-- The pair quadratic value from the pair coordinates. -/
private def pairQ (s : Fin 2) (a b : Fin 24) : ℤ :=
  let u : Fin 24 → ℤ := fun i =>
    4 * (if i = a then 1 else 0) + (if s = 0 then -4 else 4) * (if i = b then 1 else 0)
  288 + 2 * (∑ i, sixthV i * u i) ^ 2 + 6 * (∑ i, sixthW i * u i) ^ 2

/-- The pair numerator from the pair coordinates. -/
private def pairN (s : Fin 2) (a b : Fin 24) : ℤ :=
  (if s = 0 then 1 else -1) * generatedSixthNormEightVectorData 8 a *
      generatedSixthNormEightVectorData 8 b +
    4 * (generatedSixthMiddlePairNumerator 0 a b - generatedSixthMiddlePairNumerator 1 a b)

private def pairZero (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Prop :=
  pairQ s a b = 32 * (if c = 0 then 1 else -1) * pairN s a b

private instance (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Decidable (pairZero s a b c) := by
  unfold pairZero
  infer_instance

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedSixthAxis = 0 ↔
      pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c := by
  rw [sixth_zero_iff _ c _ (generatedSixth_final_pair_coordinate s p), sixth_quad]
  have h := griessShortIntegral_squareSum (Sum.inl (s, p))
  unfold leechSquareSum at h
  rw [h]
  rfl

/-- Exactly one actual pair address is orthogonal to the Sixth prototype. -/
private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2) generatedSixthAxis = 0).card = 1 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 q.2 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  decide +kernel

private theorem octad_card :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2) generatedSixthAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact sixth_octad_ne q.1.1 q.1.2 q.2

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2) generatedSixthAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact sixth_odd_ne q.1.1 q.1.2 q.2

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) generatedSixthAxis = 0).card = 1 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) generatedSixthAxis = 0)
  rw [pair_card, octad_card, odd_card] at h
  exact h

/-- Exactly one actual signed-short axis is orthogonal to the actual Sixth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_sixth :
    generatedFeasibleAmbientAxisZeroCount generatedSixthAxis = 1 := by
  rw [generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
