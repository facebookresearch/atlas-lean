/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagMatrixFixing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagAnchorFixing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7MonomialSignPhaseRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7AnchorMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitMatrixAssembly

/-! Exact entire original signed anchor enumeration and actual Tenth matrix order. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual short-root anchor stabilizer inside the entire actual matrix group. -/
abbrev generatedTenthE7ActualAnchorStabilizer :=
  MulAction.stabilizer generatedTenthE7StandardMatrixGroup (generatedTenthE7RootShortLabelEquiv 0)

/-- Every complete original signed candidate gives an actual whole matrix and short-root fixer. -/
def generatedTenthE7SignedAnchorEnumeration (v : generatedTenthE7SignedFlagCandidates) :
    generatedTenthE7ActualAnchorStabilizer :=
  ⟨⟨generatedTenthE7SignedFlagSpatial v, generatedTenth_e7_signed_flag_matrix_mem v⟩, by
    apply Subtype.ext
    change griessShortPermutation (generatedTenthE7SignedFlagSpatial v)
      (generatedTenthE7OrbitNodeLabel 0) = generatedTenthE7OrbitNodeLabel 0
    apply griessShortClass_injective
    rw [griessShortPermutation_class, ← generatedTenth_e7_orbit_node_class_actual,
      generatedTenth_e7_signed_flag_anchor_class]⟩

/-- Distinct complete candidates remain distinct in the entire actual anchor stabilizer. -/
theorem generatedTenth_e7_signed_anchor_enumeration_injective :
    Function.Injective generatedTenthE7SignedAnchorEnumeration := by
  intro v w h
  exact generatedTenth_e7_signed_flag_spatial_injective
    (congrArg (fun g : generatedTenthE7ActualAnchorStabilizer => g.val.val) h)

/-- Every actual whole matrix and short-root fixer is one of the full original signed candidates. -/
theorem generatedTenth_e7_signed_anchor_enumeration_surjective :
    Function.Surjective generatedTenthE7SignedAnchorEnumeration := by
  intro g
  obtain ⟨c, p, hg⟩ := generatedTenth_e7_anchor_stabilizer_monomial g
  have hm : g.val.val = golayMonomialPair (c, p) := hg
  have he : generatedTenthE7MonomialProjectionFixes c p := by
    intro x
    rw [← hm]
    exact generatedTenth_e7_root_orbit_standard_commute g.val x
  have hl : generatedTenthE7MonomialLineFixes c p := by
    unfold generatedTenthE7MonomialLineFixes
    rw [← hm]
    exact generatedTenth_e7_standard_matrix_norm_line g.val
  let q := generatedTenthE7MonomialFlagPermutation c p he hl
  have hc : generatedTenthE7StandardTwistedSignCondition (generatedTenthE7SignedFlagPhase q) c :=
    generatedTenth_e7_monomial_flag_sign_condition c q he hl
  refine ⟨⟨q, ⟨c, hc⟩⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hm.symm

/-- The complete92160 original signed candidates biject with the entire actual anchor stabilizer. -/
def generatedTenthE7SignedAnchorEquiv :
    generatedTenthE7SignedFlagCandidates ≃ generatedTenthE7ActualAnchorStabilizer :=
  Equiv.ofBijective generatedTenthE7SignedAnchorEnumeration
    ⟨generatedTenth_e7_signed_anchor_enumeration_injective,
      generatedTenth_e7_signed_anchor_enumeration_surjective⟩

/-- The entire actual original short-root anchor stabilizer has exactly92160 elements. -/
theorem generatedTenth_e7_actual_anchor_stabilizer_card :
    Nat.card generatedTenthE7ActualAnchorStabilizer = 92160 := by
  rw [← Nat.card_congr generatedTenthE7SignedAnchorEquiv,
    generatedTenth_e7_signed_flag_candidates_card]

/-- The entire original actual Co0 matrix stabilizer has exactly5806080 elements. -/
theorem generatedTenth_e7_actual_original_matrix_stabilizer_card :
    Nat.card generatedTenthE7OriginalMatrixGroup = 5806080 := by
  rw [generatedTenth_e7_original_matrix_card_root_factor
    (generatedTenthE7RootShortLabelEquiv 0),
    generatedTenth_e7_actual_anchor_stabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
