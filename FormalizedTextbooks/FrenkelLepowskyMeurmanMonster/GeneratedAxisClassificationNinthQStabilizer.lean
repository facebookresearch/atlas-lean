/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTensorColumnCoordinate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthFinalColumnFacts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthTensorSupportCriterion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLocalStabilizer

/-! The original normalized tensor column excludes every nonidentity extraspecial
full-axis fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A unique squared coordinate occurs in the actual normalized tensor column. -/
theorem generatedNinth_tensor_column_unique_square :
    ∃ t : SpinIndex, ∀ u : SpinIndex,
      (generatedNinthTensorColumn u) ^ 2 = (generatedNinthTensorColumn t) ^ 2 → u = t := by
  refine ⟨golayLabelCoefficients 1177, ?_⟩
  intro u hu
  rw [generatedNinth_tensor_column, generatedNinth_tensor_column,
    nortonUIntegerLabel_coeff] at hu
  have ht : (generatedNinthFinalColumnInteger 1177) ^ 2 = 324 :=
    (generatedNinth_final_column_square_iff 1177).mpr rfl
  have he : (generatedNinthFinalColumnInteger (nortonUIntegerLabel u)) ^ 2 = 324 := by
    have hs : (generatedNinthFinalColumnInteger (nortonUIntegerLabel u)) ^ 2 =
        (generatedNinthFinalColumnInteger 1177) ^ 2 := by exact_mod_cast hu
    exact hs.trans ht
  have hn : nortonUIntegerLabel u = 1177 :=
    Fin.ext ((generatedNinth_final_column_square_iff _).mp he)
  rw [← nortonUIntegerLabel_inverse u, hn]

/-- All thirteen original detecting coordinates occur nontrivially in the actual tensor. -/
theorem generatedNinth_tensor_column_detecting_nonzero (i : Fin 13) :
    generatedNinthTensorColumn
      (golayLabelCoefficients (generatedNinthTensorSupportLabels i)) ≠ 0 := by
  rw [generatedNinth_tensor_column, nortonUIntegerLabel_coeff]
  exact_mod_cast generatedNinth_final_column_detecting_nonzero i

/-- A full-axis extraspecial fixer fixes the original normalized spin column. -/
theorem generatedNinth_axis_Q_fixed_trivial (q : Q)
    (hq : rhoLocal (inclQ q) generatedNinthAxis = generatedNinthAxis) : q = 1 := by
  have hf := ((generatedFourthQ_full_fixed_iff q generatedNinthAxis).mp hq).2 1
  have hc : spinRepresentation q generatedNinthTensorColumn = generatedNinthTensorColumn := by
    change spinRepresentation q
      ((64 * Real.sqrt 2) • fun t => (griessConwayEncode generatedNinthAxis).2.2 t 1) =
        (64 * Real.sqrt 2) • fun t => (griessConwayEncode generatedNinthAxis).2.2 t 1
    rw [map_smul, hf]
  exact generatedNinth_tensor_support_fixed_trivial q generatedNinthTensorColumn hc
    generatedNinth_tensor_column_unique_square generatedNinth_tensor_column_detecting_nonzero

/-- The genuine full-axis extraspecial stabilizer is trivial. -/
theorem generatedNinthAxisQStabilizer_eq_bot : generatedNinthAxisQStabilizer = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro q hq
  exact generatedNinth_axis_Q_fixed_trivial q hq

/-- Exactly one actual extraspecial element fixes the entire ninth axis. -/
theorem generatedNinthAxisQStabilizer_card : Nat.card generatedNinthAxisQStabilizer = 1 := by
  rw [generatedNinthAxisQStabilizer_eq_bot]
  exact Subgroup.card_bot

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
