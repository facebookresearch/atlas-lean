/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootCatalogueSource

/-! The entire actual perpendicular root-line catalogue, with completeness transported
from the previously proved complete E8 catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The original genuine lattice isometry carrying Fifth's catalogue to the standard octad. -/
def generatedTenthE7RootCatalogueIsometry : leechIsomSubgroup :=
  golayPermutationIsometry generatedTenthE7RootCataloguePermutation⁻¹

/-- The entire actual E8 lattice section transported by that original isometry. -/
def generatedTenthE7StandardE8Section : Submodule ℤ leechIntegral :=
  (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)).map
    (leechIntegralAction generatedTenthE7RootCatalogueIsometry).toLinearMap

/-- The original complete E8 short-line bijection transported by the genuine action. -/
def generatedTenthE7StandardE8RootLabelEquiv : Fin 120 ≃
    generatedAxisE8ShortLines generatedTenthE7StandardE8Section :=
  leechSeventhE8RootLabelEquiv.trans (generatedAxisE8ShortLinesEquiv
    generatedTenthE7RootCatalogueIsometry
      (generatedAxisE8CoordinateSection (golayOctadWord generatedFifthFlagOctad)))

private theorem label_apply (r : Fin 120) :
    (generatedTenthE7StandardE8RootLabelEquiv r).val =
      griessShortPermutation generatedTenthE7RootCatalogueIsometry (leechSeventhE8RootLabel r) :=
  rfl

/-- Every actual root equals the original preferred representative with one of its two signs. -/
theorem generatedTenth_e7_standard_e8_root_label_sign (r : Fin 120) :
    generatedTenthE7StandardE8Root r =
        griessShortLatticeVector (generatedTenthE7StandardE8RootLabelEquiv r).val ∨
      generatedTenthE7StandardE8Root r =
        -griessShortLatticeVector (generatedTenthE7StandardE8RootLabelEquiv r).val := by
  rw [label_apply]
  rcases leechSeventhE8Root_label_sign r with h | h
  · change leechIntegralAction generatedTenthE7RootCatalogueIsometry (leechSeventhE8Root r) = _ ∨
      leechIntegralAction generatedTenthE7RootCatalogueIsometry (leechSeventhE8Root r) = _
    rw [h]
    exact generatedE8Short_integral_sign _ _
  · change leechIntegralAction generatedTenthE7RootCatalogueIsometry (leechSeventhE8Root r) = _ ∨
      leechIntegralAction generatedTenthE7RootCatalogueIsometry (leechSeventhE8Root r) = _
    rw [h, map_neg]
    rcases generatedE8Short_integral_sign generatedTenthE7RootCatalogueIsometry
        (leechSeventhE8RootLabel r) with ht | ht
    · exact Or.inr (by rw [ht])
    · exact Or.inl (by rw [ht, neg_neg])

/-- All actual preferred short lines in that complete section perpendicular to e4+e5. -/
def generatedTenthE7StandardRootLines :=
  {r : generatedAxisE8ShortLines generatedTenthE7StandardE8Section //
    (griessShortLatticeVector r.val).val 4 + (griessShortLatticeVector r.val).val 5 = 0}

/-- Original finite perpendicularity is precisely actual preferred-root perpendicularity. -/
theorem generatedTenth_e7_standard_root_index_condition (r : Fin 120) :
    r ∈ generatedTenthE7OrbitRootIndices ↔
      (griessShortLatticeVector (generatedTenthE7StandardE8RootLabelEquiv r).val).val 4 +
        (griessShortLatticeVector (generatedTenthE7StandardE8RootLabelEquiv r).val).val 5 = 0 := by
  have hc : (generatedTenthE7StandardE8Root r).val 4 +
      (generatedTenthE7StandardE8Root r).val 5 =
        leechSeventhE8RootLocal r 4 + leechSeventhE8RootLocal r 5 := by
    rw [generatedTenth_e7_standard_e8_root_physical]
    simp [generatedTenthE7RootCatalogueInsert]
  simp only [generatedTenthE7OrbitRootIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hc]
  rcases generatedTenth_e7_standard_e8_root_label_sign r with h | h
  · rw [h]
  · rw [h]
    change -((griessShortLatticeVector _).val 4) +
      -((griessShortLatticeVector _).val 5) = 0 ↔ _
    rw [← neg_add, neg_eq_zero]

/-- The sixty-three complete source addresses biject with the entire actual perpendicular set. -/
def generatedTenthE7StandardRootLineEquiv : Fin 63 ≃ generatedTenthE7StandardRootLines :=
  generatedTenthE7OrbitRootIndexEquiv.trans
    (generatedTenthE7StandardE8RootLabelEquiv.subtypeEquiv
      generatedTenth_e7_standard_root_index_condition)

/-- Exactly sixty-three actual preferred short lines occur in the entire perpendicular E7 set. -/
theorem generatedTenth_e7_standard_root_lines_card : Nat.card generatedTenthE7StandardRootLines =
    63 := by
  rw [← Nat.card_congr generatedTenthE7StandardRootLineEquiv]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
