/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNewDestinationSeparation

/-! Original selected-square formulas for every preferred short-vector family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original source label 2063 is exactly the first eight physical coordinates. -/
theorem generatedFeasibleContaining_selected_source_word :
    golayOctadWord generatedFeasibleContainingOctadPrototypeIndex = golayStandardOctad := by
  unfold golayOctadWord
  rw [generatedFeasibleContainingOctadPrototypeIndex_label]
  decide +kernel

/-- Actual selected short-vector squares, measured in the original integer normalization. -/
def generatedFeasibleContainingSelectedShortSquare (r : GriessShortIndex) : ℤ :=
  generatedFeasibleContainingSelectedSquare
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) (griessShortIntegral r)

private theorem selected_sum (u : Fin 24 → ℤ) :
    generatedFeasibleContainingSelectedSquare
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) u =
        ∑ i : Fin 24, if i.val < 8 then u i ^ 2 else 0 := by
  rw [generatedFeasibleContaining_selected_source_word]
  unfold generatedFeasibleContainingSelectedSquare
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < 8
  · have hb : golayStandardOctad i = 1 := by simp [golayStandardOctad, hi]
    rw [hb, ite_eq_left hi]
    rw [show ((1 : ZMod 2).val : ℤ) = 1 from by decide +kernel]
    exact one_mul _
  · have hb : golayStandardOctad i = 0 := by simp [golayStandardOctad, hi]
    rw [hb, ite_eq_right hi]
    simp

/-- The pair selected square depends only on its two original physical support positions. -/
theorem generatedFeasibleContainingSelectedShortSquare_pair (s : Fin 2) (p : Fin 276) :
    generatedFeasibleContainingSelectedShortSquare (Sum.inl (s, p)) =
      16 * (if (griessCoordinatePair p).1.val < 8 then 1 else 0) +
        16 * (if (griessCoordinatePair p).2.val < 8 then 1 else 0) := by
  rw [generatedFeasibleContainingSelectedShortSquare, selected_sum]
  have hp := griessCoordinatePair_ne p
  have he (i : Fin 24) :
      (if i.val < 8 then griessShortIntegral (Sum.inl (s, p)) i ^ 2 else 0) =
        (if i = (griessCoordinatePair p).1 then
          16 * (if (griessCoordinatePair p).1.val < 8 then 1 else 0) else 0) +
        (if i = (griessCoordinatePair p).2 then
          16 * (if (griessCoordinatePair p).2.val < 8 then 1 else 0) else 0) := by
    by_cases ha : i = (griessCoordinatePair p).1
    · subst i
      by_cases hs : s = 0 <;> by_cases hi : (griessCoordinatePair p).1.val < 8 <;>
        simp [griessShortIntegral, hp, hs, hi]
    · by_cases hb : i = (griessCoordinatePair p).2
      · subst i
        by_cases hs : s = 0 <;> by_cases hi : (griessCoordinatePair p).2.val < 8 <;>
          simp [griessShortIntegral, hp.symm, hs, hi]
      · simp [griessShortIntegral, ha, hb]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

/-- Actual selected octad squares are four times its original occupied source coordinates. -/
theorem generatedFeasibleContainingSelectedShortSquare_octad (o : Fin 759) (e : Fin 64) :
    generatedFeasibleContainingSelectedShortSquare (Sum.inr (Sum.inl (o, e))) =
      4 * ∑ i : Fin 24, if i.val < 8 ∧
        (golayEncodedMask (golayOctadLabel o).val).testBit i.val then (1 : ℤ) else 0 := by
  rw [generatedFeasibleContainingSelectedShortSquare, selected_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [griessShortIntegral]
  split_ifs <;> simp_all

/-- Actual selected odd squares depend only on the original exceptional physical position. -/
theorem generatedFeasibleContainingSelectedShortSquare_odd (d : Fin 2048) (j : Fin 24) :
    generatedFeasibleContainingSelectedShortSquare (Sum.inr (Sum.inr (d, j))) =
      8 + 8 * (if j.val < 8 then 1 else 0) := by
  rw [generatedFeasibleContainingSelectedShortSquare, selected_sum]
  have he (i : Fin 24) :
      (if i.val < 8 then griessShortIntegral (Sum.inr (Sum.inr (d, j))) i ^ 2 else 0) =
        (if i.val < 8 then (1 : ℤ) else 0) +
          8 * (if i = j then (if j.val < 8 then 1 else 0) else 0) := by
    by_cases hij : i = j
    · subst i
      by_cases hi : j.val < 8 <;> cases hb : (golayEncodedMask d.val).testBit j.val <;>
        simp [griessShortIntegral, hi, hb]
    · by_cases hi : i.val < 8 <;> cases hb : (golayEncodedMask d.val).testBit i.val <;>
        simp [griessShortIntegral, hi, hij, hb]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : (∑ i : Fin 24, if i.val < 8 then (1 : ℤ) else 0) = 8 := by decide +kernel
  rw [hc]
  simp

/-- Original selected-square bins, before adding the fixed root's square thirty-two. -/
def generatedFeasibleContainingSelectedShortValues : Fin 4 → ℤ := ![0, 8, 16, 32]

/-- Finite physical pair counts, transported later through the genuine pair address equivalence.
-/
def generatedFeasibleContainingSelectedPairPhysicalCount (k : Fin 4) : ℕ :=
  ∑ z : Fin 2 × griessCoordinatePairs,
    if ((4 * (if (0 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (0 : Fin 24) = z.2.val.2 then 1 else 0)) =
      (4 * (if (1 : Fin 24) = z.2.val.1 then (1 : ℤ) else 0) +
        (if z.1 = 0 then -4 else 4) * (if (1 : Fin 24) = z.2.val.2 then 1 else 0))) ∧
      16 * (if z.2.val.1.val < 8 then (1 : ℤ) else 0) +
        16 * (if z.2.val.2.val < 8 then 1 else 0) =
          generatedFeasibleContainingSelectedShortValues k then 1 else 0

set_option maxHeartbeats 16000000 in
-- Check every original increasing physical coordinate pair and both preferred sign families.
/-- The complete preferred pair contribution is 240, zero, 192 and thirty-one. -/
theorem generatedFeasibleContainingSelectedPairPhysicalCount_eq (k : Fin 4) :
    generatedFeasibleContainingSelectedPairPhysicalCount k =
      (![240, 0, 192, 31] : Fin 4 → ℕ) k := by
  have h : ∀ k : Fin 4, generatedFeasibleContainingSelectedPairPhysicalCount k =
      (![240, 0, 192, 31] : Fin 4 → ℕ) k := by decide +kernel
  exact h k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
