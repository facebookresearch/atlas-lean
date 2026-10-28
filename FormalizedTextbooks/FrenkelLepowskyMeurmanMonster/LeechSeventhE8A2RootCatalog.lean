/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Roots

/-! The finite root coordinates enumerate every actual short line in the selected section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 40000000 in
-- Compare all 14400 root pairs on their eight literal coordinates, allowing both signs.
/-- No two distinct finite representatives define the same genuine unoriented root line. -/
theorem leechSeventhE8RootLocal_sign_unique : ∀ r s : Fin 120,
    leechSeventhE8RootLocal r = leechSeventhE8RootLocal s ∨
      leechSeventhE8RootLocal r = -leechSeventhE8RootLocal s → r = s := by
  decide +kernel

private theorem insert_read (v : Fin 8 → ℤ) (j : Fin 8) :
    generatedFifthFrameInsert v (generatedFifthFramePositions j) = v j := by
  fin_cases j <;> simp [generatedFifthFrameInsert, generatedFifthFramePositions]

private theorem insert_injective : Function.Injective generatedFifthFrameInsert := by
  intro v w h
  ext j
  exact (insert_read v j).symm.trans ((congrFun h _).trans (insert_read w j))

/-- Every genuine finite root is physically supported on the selected original octad. -/
theorem leechSeventhE8Root_supported (r : Fin 120) :
    leechSeventhE8Root r ∈
      generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad) := by
  change ∀ i, golayOctadWord generatedFifthFlagOctad i = 0 →
    (leechSeventhE8Root r).val i = 0
  intro i hi
  have h := (generatedFifthFrame_word_zero i).mp hi
  rw [leechSeventhE8Root_physical]
  simp [generatedFifthFrameInsert, (not_or.mp h).1, (not_or.mp h).2]

/-- The original short catalogue label of a genuine root, with its orientation forgotten. -/
def leechSeventhE8RootLabel (r : Fin 120) : GriessShortIndex :=
  Classical.choose (leechShort_catalog (leechSeventhE8Root r) (leechSeventhE8Root_norm r))

/-- The chosen label is the original root representative with its actual possible sign. -/
theorem leechSeventhE8Root_label_sign (r : Fin 120) :
    leechSeventhE8Root r = griessShortLatticeVector (leechSeventhE8RootLabel r) ∨
      leechSeventhE8Root r = -griessShortLatticeVector (leechSeventhE8RootLabel r) := by
  have h := Classical.choose_spec
    (leechShort_catalog (leechSeventhE8Root r) (leechSeventhE8Root_norm r))
  rcases h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- The finite label is exactly the genuine reduction of its lattice representative. -/
theorem leechSeventhE8Root_label_class (r : Fin 120) :
    griessShortClass (leechSeventhE8RootLabel r) = leechReduction (leechSeventhE8Root r) := by
  rcases leechSeventhE8Root_label_sign r with h | h
  · rw [h]
    rfl
  · rw [h, leechReduction_neg]
    rfl

/-- Each finite label lies in the actual section's original short-line incidence set. -/
theorem leechSeventhE8Root_label_supported (r : Fin 120) :
    leechSeventhE8RootLabel r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) := by
  have h := leechSeventhE8Root_supported r
  rcases leechSeventhE8Root_label_sign r with hr | hr
  · rw [hr] at h
    exact h
  · rw [hr, Submodule.neg_mem_iff] at h
    exact h

/-- The genuine root labels are injectively parametrized by the finite 120 addresses. -/
theorem leechSeventhE8RootLabel_injective : Function.Injective leechSeventhE8RootLabel := by
  intro r s h
  have hc : leechReduction (leechSeventhE8Root r) =
      leechReduction (leechSeventhE8Root s) := by
    rw [← leechSeventhE8Root_label_class, ← leechSeventhE8Root_label_class, h]
  have hr := leechShort_same_class (leechSeventhE8Root r) (leechSeventhE8Root s)
    (leechSeventhE8Root_norm r) (leechSeventhE8Root_norm s) hc
  apply leechSeventhE8RootLocal_sign_unique r s
  rcases hr with hr | hr
  · left
    apply insert_injective
    exact (leechSeventhE8Root_physical r).symm.trans
      ((congrArg Subtype.val hr).trans (leechSeventhE8Root_physical s))
  · right
    apply insert_injective
    rw [map_neg]
    have he := congrArg Subtype.val hr
    simpa only [leechSeventhE8Root_physical, Submodule.coe_neg] using he

/-- The finite parametrization covers every actual short line of the selected section. -/
def leechSeventhE8RootLabelEquiv : Fin 120 ≃ generatedAxisE8ShortLines
    (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)) :=
  Equiv.ofBijective (fun r => ⟨leechSeventhE8RootLabel r, leechSeventhE8Root_label_supported r⟩)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨by
      intro r s h
      exact leechSeventhE8RootLabel_injective (congrArg Subtype.val h), by
      rw [generatedAxisE8ShortLines_coordinate_card]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]⟩)

/-- The finite signed action induces exactly the original spatial short-label action. -/
theorem leechSeventhE8Root_label_action (g : Fin 18) (r : Fin 120) :
    griessShortPermutation (generatedFifthSectionGenerator g) (leechSeventhE8RootLabel r) =
      leechSeventhE8RootLabel (leechSeventhE8RootImage g r) := by
  apply griessShortClass_injective
  rw [griessShortPermutation_class, leechSeventhE8Root_label_class,
    leechSeventhE8Root_label_class]
  change leechReduction
    (leechIntegralAction (generatedFifthSectionGenerator g) (leechSeventhE8Root r)) = _
  rw [leechSeventhE8Root_action]
  rcases leechSeventhE8Root_sign_certificate g r with h | h
  · rw [h, one_smul]
  · rw [h, neg_one_smul, leechReduction_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
