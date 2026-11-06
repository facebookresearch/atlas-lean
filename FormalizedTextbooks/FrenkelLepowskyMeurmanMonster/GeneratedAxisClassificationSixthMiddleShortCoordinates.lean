/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The actual middle short block is supported on 552 transported preferred pair addresses. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original pair-address carrier, retaining both preferred signed lines. -/
abbrev GeneratedSixthSourcePair := Fin 2 × Fin 276

/-- The genuine forward short label from every original pair address. -/
def generatedSixthMiddleShortLabel (p : GeneratedSixthSourcePair) : GriessShortIndex :=
  griessShortPermutation generatedSixthLocalFiber.val.2 (Sum.inl p)

/-- The genuine preferred-Q phase from the original full local word. -/
def generatedSixthMiddleShortPhase (p : GeneratedSixthSourcePair) : ZMod 2 :=
  localShortPhase generatedSixthLocalFiber (Sum.inl p)

/-- The original integer coefficient numerator before the local permutation. -/
def generatedSixthSourceShortWeight (p : GeneratedSixthSourcePair) : ℤ :=
  (if p.1 = 0 then 1 else -1) *
    griessShortIntegral (Sum.inr (Sum.inr (0,0))) (griessCoordinatePair p.2).1 *
    griessShortIntegral (Sum.inr (Sum.inr (0,0))) (griessCoordinatePair p.2).2

private theorem short_product (a b : ℝ) :
    2 * (a / Real.sqrt 8) * (b / Real.sqrt 8) = a * b / 4 := by
  have hs : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  calc
    _ = 2 * a * b / (Real.sqrt 8) ^ 2 := by ring
    _ = _ := by rw [hs]; ring

/-- Every original pair input has its exact, normalized integer coefficient. -/
theorem generatedSixth_source_short_pair_numerator (p : GeneratedSixthSourcePair) :
    (griessConwayEncode generatedOddAxis).2.1 (Sum.inl p) =
      (generatedSixthSourceShortWeight p : ℝ) / 4 := by
  rcases p with ⟨s,p⟩
  have h := generatedAxis_triality_odd_pair_coordinate 0 0 0 s p
  change (griessConwayEncode generatedOddAxis).2.1 (Sum.inl (s,p)) = _ at h
  rw [h]
  simp only [griessShortVector, short_product, generatedSixthSourceShortWeight,
    Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg]
  ring

/-- Each actual transported coordinate has the original coefficient and full preferred-Q phase. -/
theorem generatedSixth_middle_short_coefficient (p : GeneratedSixthSourcePair) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (generatedSixthMiddleShortLabel p) =
      qSign (generatedSixthMiddleShortPhase p) *
        (generatedSixthSourceShortWeight p : ℝ) / 4 := by
  rw [generatedFourth_local_short]
  unfold generatedSixthMiddleShortLabel generatedSixthMiddleShortPhase
  rw [localShortOperator_image, generatedSixth_source_short_pair_numerator]
  ring

/-- The 552 genuine transported preferred short labels are pairwise distinct. -/
theorem generatedSixth_middle_short_label_injective :
    Function.Injective generatedSixthMiddleShortLabel := by
  intro p q hpq
  exact Sum.inl.inj ((griessShortPermutation generatedSixthLocalFiber.val.2).injective hpq)

/-- Every original middle short coefficient outside these actual addresses is zero. -/
theorem generatedSixth_middle_short_zero (r : GriessShortIndex)
    (hr : ¬ ∃ p : GeneratedSixthSourcePair, generatedSixthMiddleShortLabel p = r) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1 r = 0 := by
  let e := griessShortPermutation generatedSixthLocalFiber.val.2
  obtain ⟨a, rfl⟩ := e.surjective r
  rw [generatedFourth_local_short, localShortOperator_image]
  rcases a with p | (⟨o,s⟩ | ⟨d,i⟩)
  · exact False.elim (hr ⟨p,rfl⟩)
  · have h : (griessConwayEncode generatedOddAxis).2.1 (Sum.inr (Sum.inl (o,s))) = 0 :=
      generatedAxis_triality_odd_octad_coordinate 0 0 0 o s
    rw [h, mul_zero]
  · have h : (griessConwayEncode generatedOddAxis).2.1 (Sum.inr (Sum.inr (d,i))) = 0 :=
      generatedAxis_triality_odd_odd_coordinate 0 d 0 i 0
    rw [h, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
