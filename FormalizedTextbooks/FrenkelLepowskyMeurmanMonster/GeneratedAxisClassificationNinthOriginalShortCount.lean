/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPreferredPairs

/-! Count the genuinely nonzero original short rows before the ninth local word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original nonzero signed-pair rows. -/
abbrev generatedNinthOriginalPairSupport :=
  {r : Fin 2 × Fin 276 // generatedNinthOriginalShortNumerator (Sum.inl r) ≠ 0}

/-- The nonzero original source labels, retaining the actual signed numerators. -/
abbrev generatedNinthOriginalShortSupport :=
  {a : generatedNinthOriginalShortLabel // generatedNinthOriginalShortNumerator a ≠ 0}

/-- Every original octad source row has a signed numerator of absolute value two. -/
theorem generatedNinth_original_octad_numerator_abs (j : Fin 56) (e : Fin 64) :
    |generatedNinthOriginalShortNumerator (Sum.inr (j, e))| = 2 := by
  change |generatedFifthFinalOctadNumerator j e| = 2
  unfold generatedFifthFinalOctadNumerator trialityIntegerMatrix trialityIntegerDiagonal
    trialityHadamard
  split_ifs <;> norm_num

/-- Every original octad label is genuinely nonzero. -/
theorem generatedNinth_original_octad_numerator_ne_zero (j : Fin 56) (e : Fin 64) :
    generatedNinthOriginalShortNumerator (Sum.inr (j, e)) ≠ 0 := by
  intro h
  have ha := generatedNinth_original_octad_numerator_abs j e
  rw [h, abs_zero] at ha
  norm_num at ha

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Count only the552 genuine preferred pair labels using the checked original projector.
/-- Exactly272 original pair rows have nonzero signed numerators. -/
theorem generatedNinth_original_pair_support_card :
    Fintype.card generatedNinthOriginalPairSupport = 272 := by
  have hc : (∑ r : Fin 2 × Fin 276,
      if generatedNinthOriginalShortNumerator (Sum.inl r) ≠ 0 then 1 else 0) =
        (272 : ℕ) := by
    simp only [generatedNinthOriginalShortNumerator]
    simp_rw [generatedNinth_coordinate_pair_actual]
    decide +kernel
  rw [Fintype.card_subtype, Finset.card_filter]
  exact hc

/-- Nonzero source labels split into the counted pair support and all genuine octad signs. -/
def generatedNinthOriginalShortSupportEquiv :
    generatedNinthOriginalShortSupport ≃
      generatedNinthOriginalPairSupport ⊕ (Fin 56 × Fin 64) where
  toFun a := match a with
    | ⟨Sum.inl r, h⟩ => Sum.inl ⟨r, h⟩
    | ⟨Sum.inr r, _⟩ => Sum.inr r
  invFun a := match a with
    | Sum.inl r => ⟨Sum.inl r.val, r.property⟩
    | Sum.inr r => ⟨Sum.inr r, generatedNinth_original_octad_numerator_ne_zero r.1 r.2⟩
  left_inv a := by rcases a with ⟨a, h⟩; cases a <;> rfl
  right_inv a := by cases a <;> rfl

/-- The complete original nonzero short-source catalogue has3856 rows. -/
theorem generatedNinth_original_short_support_card :
    Fintype.card generatedNinthOriginalShortSupport = 3856 := by
  rw [Fintype.card_congr generatedNinthOriginalShortSupportEquiv,
    Fintype.card_sum, generatedNinth_original_pair_support_card]
  norm_num [Fintype.card_prod]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
