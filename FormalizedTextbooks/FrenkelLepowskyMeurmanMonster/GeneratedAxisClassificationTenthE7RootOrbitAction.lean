/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitPredicate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitReachability

/-! Genuine full matrix-group action on the entire actual sixty-three-root set. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire original traversal is a bijection with the actual preferred root-line set. -/
def generatedTenthE7RootShortLabelEquiv : Fin 63 ≃ generatedTenthE7RootShortSet :=
  generatedTenthE7OrbitOrderEquiv.trans
    (generatedTenthE7StandardRootLineEquiv.trans generatedTenthE7RootShortCatalogueEquiv)

/-- Each actual bijection value retains its exact original preferred source label. -/
theorem generatedTenth_e7_root_short_label_actual (n : Fin 63) :
    (generatedTenthE7RootShortLabelEquiv n).val = generatedTenthE7OrbitNodeLabel n := rfl

/-- Full actual preferred root incidence is equivalent before and after the genuine action. -/
theorem generatedTenth_e7_root_short_predicate_iff
    (g : generatedTenthE7StandardMatrixGroup) (r : GriessShortIndex) :
    generatedTenthE7RootShortPredicate r ↔
      generatedTenthE7RootShortPredicate (griessShortPermutation g.val r) := by
  constructor
  · exact generatedTenth_e7_root_short_preserved g r
  · intro hr
    have h := generatedTenth_e7_root_short_preserved g⁻¹ (griessShortPermutation g.val r) hr
    have he : griessShortPermutation g.val⁻¹ (griessShortPermutation g.val r) = r := by
      rw [map_inv]
      exact Equiv.symm_apply_apply _ _
    change generatedTenthE7RootShortPredicate
      (griessShortPermutation g.val⁻¹ (griessShortPermutation g.val r)) at h
    rw [he] at h
    exact h

/-- The actual whole matrix group's restriction to its entire actual E7 root set. -/
def generatedTenthE7RootShortPermutation : generatedTenthE7StandardMatrixGroup →*
    Equiv.Perm generatedTenthE7RootShortSet where
  toFun g := (griessShortPermutation g.val).subtypeEquiv
    (generatedTenth_e7_root_short_predicate_iff g)
  map_one' := by
    apply Equiv.ext
    intro r
    apply Subtype.ext
    change griessShortPermutation 1 r.val = r.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro r
    apply Subtype.ext
    change griessShortPermutation (g.val * h.val) r.val =
      griessShortPermutation g.val (griessShortPermutation h.val r.val)
    rw [map_mul]
    rfl

instance : MulAction generatedTenthE7StandardMatrixGroup generatedTenthE7RootShortSet :=
  MulAction.compHom generatedTenthE7RootShortSet generatedTenthE7RootShortPermutation

/-- The whole actual matrix group is genuinely transitive on the entire actual E7 root set. -/
theorem generatedTenth_e7_root_short_transitive (r s : generatedTenthE7RootShortSet) :
    ∃ g : generatedTenthE7StandardMatrixGroup, g • r = s := by
  obtain ⟨i, rfl⟩ := generatedTenthE7RootShortLabelEquiv.surjective r
  obtain ⟨j, rfl⟩ := generatedTenthE7RootShortLabelEquiv.surjective s
  obtain ⟨g, hg⟩ := generatedTenth_e7_root_orbit_between i j
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change griessShortPermutation g.val (generatedTenthE7OrbitNodeLabel i) =
    generatedTenthE7OrbitNodeLabel j
  apply griessShortClass_injective
  rw [griessShortPermutation_class, ← generatedTenth_e7_orbit_node_class_actual,
    hg, generatedTenth_e7_orbit_node_class_actual]

/-- Each actual whole-group orbit covers all genuine roots in the complete E7 catalogue. -/
theorem generatedTenth_e7_root_short_orbit (r : generatedTenthE7RootShortSet) :
    MulAction.orbit generatedTenthE7StandardMatrixGroup r = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro s
  exact generatedTenth_e7_root_short_transitive r s

/-- The actual full matrix group's root orbit has precisely sixty-three elements. -/
theorem generatedTenth_e7_root_short_orbit_card (r : generatedTenthE7RootShortSet) :
    Nat.card (MulAction.orbit generatedTenthE7StandardMatrixGroup r) = 63 := by
  rw [generatedTenth_e7_root_short_orbit, Nat.card_univ, generatedTenth_e7_root_short_set_card]

/-- Actual orbit-stabilizer decomposition with the entire genuine matrix group
and root fixer. -/
theorem generatedTenth_e7_root_short_matrix_card (r : generatedTenthE7RootShortSet) :
    Nat.card generatedTenthE7StandardMatrixGroup =
      63 * Nat.card (MulAction.stabilizer generatedTenthE7StandardMatrixGroup r) := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup generatedTenthE7StandardMatrixGroup r)
  rw [Nat.card_prod, generatedTenth_e7_root_short_orbit_card] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
