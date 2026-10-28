/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientZeroTools
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix

/-! The Fifth local family: exactly sixteen actual signed-short axes are orthogonal to the
actual Fifth prototype.

The prototype matrix is `¼ I + ¼ P` for the coordinate octad `0x0f000f`, so its quadratic
value on an actual short vector is at least 128 in units of 1/16. Octad numerators have
absolute value two and odd coordinates vanish, so only pair addresses can be orthogonal;
these 1104 addresses are checked exactly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Diagonal matrix numerators of the actual Fifth prototype, over 16. -/
def generatedFeasibleAmbientFifthDiag (i : Fin 24) : ℤ :=
  if Nat.testBit 0x0f000f i.val then 8 else 4

/-- The full matrix numerator of the actual Fifth prototype, over 16. -/
def generatedFeasibleAmbientFifthN (i j : Fin 24) : ℤ :=
  if i = j then generatedFeasibleAmbientFifthDiag i else 0

private theorem fifth_matrix (i j : Fin 24) :
    (griessConwayEncode generatedFifthAxis).1 i j =
      (generatedFeasibleAmbientFifthN i j : ℝ) / 16 := by
  rw [generatedFifth_matrix]
  unfold generatedFeasibleAmbientFifthN generatedFeasibleAmbientFifthDiag
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq, ↓reduceIte]
    split_ifs <;> norm_num
  · rw [Matrix.diagonal_apply_ne _ h]
    simp [h]

private theorem fifth_quad (u : Fin 24 → ℤ) :
    ∑ i, ∑ j, u i * generatedFeasibleAmbientFifthN i j * u j =
      ∑ i, generatedFeasibleAmbientFifthDiag i * u i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  unfold generatedFeasibleAmbientFifthN
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  ring

private theorem fifth_quad_ge (r : GriessShortIndex) :
    128 ≤ ∑ i, ∑ j, griessShortIntegral r i * generatedFeasibleAmbientFifthN i j *
      griessShortIntegral r j := by
  rw [fifth_quad]
  have h := griessShortIntegral_squareSum r
  unfold leechSquareSum at h
  calc (128 : ℤ) = 4 * ∑ i, griessShortIntegral r i ^ 2 := by rw [h]; norm_num
    _ = ∑ i, 4 * griessShortIntegral r i ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold generatedFeasibleAmbientFifthDiag
      split_ifs <;> norm_num

private theorem fifth_zero_iff (r : GriessShortIndex) (c : ZMod 2) (n : ℤ)
    (hS : (griessConwayEncode generatedFifthAxis).2.1 r = (n : ℝ) / 16) :
    griessForm (conwayShortAxis r c) generatedFifthAxis = 0 ↔
      (∑ i, ∑ j, griessShortIntegral r i * generatedFeasibleAmbientFifthN i j *
        griessShortIntegral r j) = 32 * (if c = 0 then 1 else -1) * n := by
  rw [generatedFeasibleAmbient_axis_form_eq_zero_iff_int r c generatedFifthAxis
    generatedFeasibleAmbientFifthN n 16 16 (by norm_num) (by norm_num) fifth_matrix hS]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

private theorem fifth_ne_of_small (r : GriessShortIndex) (c : ZMod 2) (n : ℤ)
    (hS : (griessConwayEncode generatedFifthAxis).2.1 r = (n : ℝ) / 16) (hn : |n| ≤ 3) :
    griessForm (conwayShortAxis r c) generatedFifthAxis ≠ 0 := by
  rw [Ne, fifth_zero_iff r c n hS]
  intro h
  have hq := fifth_quad_ge r
  rw [h] at hq
  have hb := abs_le.mp hn
  split_ifs at hq <;> linarith [hb.1, hb.2]

set_option maxRecDepth 100000 in
-- All 4096 actual octad Fourier entries are checked.
private theorem triality_entry_abs : ∀ e f : Fin 64, |trialityIntegerMatrix e f| = 1 := by
  unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
  decide +kernel

private theorem octad_numerator_abs (j : Fin 56) (e : Fin 64) :
    |generatedFifthFinalOctadNumerator j e| ≤ 3 := by
  unfold generatedFifthFinalOctadNumerator
  rw [abs_mul, abs_mul, triality_entry_abs]
  split_ifs <;> norm_num

/-- No actual octad address is orthogonal to the Fifth prototype. -/
private theorem fifth_octad_ne (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c) generatedFifthAxis ≠ 0 := by
  by_cases ho : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o
  · obtain ⟨j, rfl⟩ := ho
    exact fifth_ne_of_small _ c _ (generatedFifth_final_octad_numerator j e)
      (octad_numerator_abs j e)
  · exact fifth_ne_of_small _ c 0
      (by rw [generatedFifth_final_octad_zero o e ho]; simp) (by simp)

/-- No actual odd address is orthogonal to the Fifth prototype. -/
private theorem fifth_odd_ne (d : Fin 2048) (j : Fin 24) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inr (Sum.inr (d, j))) c) generatedFifthAxis ≠ 0 :=
  fifth_ne_of_small _ c 0 (by rw [generatedFifth_final_odd_zero d j]; simp) (by simp)

/-- The pair quadratic value from the pair coordinates. -/
private def pairQ (a b : Fin 24) : ℤ :=
  16 * (generatedFeasibleAmbientFifthDiag a + generatedFeasibleAmbientFifthDiag b)

private def pairZero (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Prop :=
  pairQ a b = 32 * (if c = 0 then 1 else -1) * generatedFifthFinalPairNumerator s a b

private instance (s : Fin 2) (a b : Fin 24) (c : ZMod 2) : Decidable (pairZero s a b c) := by
  unfold pairZero
  infer_instance

private theorem pair_quad (s : Fin 2) (p : Fin 276) :
    ∑ i, ∑ j, griessShortIntegral (Sum.inl (s, p)) i * generatedFeasibleAmbientFifthN i j *
      griessShortIntegral (Sum.inl (s, p)) j =
      pairQ (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  rw [fifth_quad]
  have hab := griessCoordinatePair_ne p
  have hu (i : Fin 24) : griessShortIntegral (Sum.inl (s, p)) i ^ 2 =
      16 * ((if i = (griessCoordinatePair p).1 then 1 else 0) +
        (if i = (griessCoordinatePair p).2 then 1 else 0)) := by
    simp only [griessShortIntegral]
    by_cases h1 : i = (griessCoordinatePair p).1 <;>
      by_cases h2 : i = (griessCoordinatePair p).2
    · exact absurd (h1.symm.trans h2) hab
    · simp [h1, hab]
    · simp [h2, hab.symm]
    · simp [h1, h2]
  simp only [hu, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, pairQ]
  ring

private theorem pair_zero_iff (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    griessForm (conwayShortAxis (Sum.inl (s, p)) c) generatedFifthAxis = 0 ↔
      pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c := by
  rw [fifth_zero_iff _ c _ (generatedFifth_final_pair_numerator s p), pair_quad]
  rfl

/-- Exactly sixteen actual pair addresses are orthogonal to the Fifth prototype. -/
private theorem pair_card :
    (Finset.univ.filter fun q : (Fin 2 × Fin 276) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inl q.1) q.2) generatedFifthAxis = 0).card = 16 := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [pair_zero_iff]
  have he (s : Fin 2) : (∑ p : Fin 276, ∑ c : ZMod 2,
      if pairZero s (griessCoordinatePair p).1 (griessCoordinatePair p).2 c then 1 else 0) =
      ∑ q ∈ griessCoordinatePairs, ∑ c : ZMod 2, if pairZero s q.1 q.2 c then 1 else 0 := by
    rw [← Finset.sum_coe_sort griessCoordinatePairs]
    exact Fintype.sum_equiv griessCoordinatePairEquiv _ _ fun _ => rfl
  simp_rw [he]
  unfold pairZero pairQ generatedFifthFinalPairNumerator generatedFifthMiddleProjectorNumerator
  decide +kernel

private theorem octad_card :
    (Finset.univ.filter fun q : (Fin 759 × Fin 64) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inl q.1)) q.2) generatedFifthAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact fifth_octad_ne q.1.1 q.1.2 q.2

private theorem odd_card :
    (Finset.univ.filter fun q : (Fin 2048 × Fin 24) × ZMod 2 =>
      griessForm (conwayShortAxis (Sum.inr (Sum.inr q.1)) q.2) generatedFifthAxis = 0).card =
      0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  exact fifth_odd_ne q.1.1 q.1.2 q.2

set_option maxRecDepth 1000000 in
-- Kernel checking of the three-family split unfolds the finite address type deeply.
private theorem total_card :
    (Finset.univ.filter fun p : GriessShortIndex × ZMod 2 =>
      griessForm (conwayShortAxis p.1 p.2) generatedFifthAxis = 0).card = 16 := by
  have h := generatedFeasibleAmbient_short_filter_card (fun r c =>
    griessForm (conwayShortAxis r c) generatedFifthAxis = 0)
  rw [pair_card, octad_card, odd_card] at h
  exact h

/-- Exactly sixteen actual signed-short axes are orthogonal to the actual Fifth prototype. -/
theorem generatedFeasibleAmbientAxisZeroCount_fifth :
    generatedFeasibleAmbientAxisZeroCount generatedFifthAxis = 16 := by
  rw [generatedFeasibleAmbientAxisZeroCount_eq_card]
  exact total_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
