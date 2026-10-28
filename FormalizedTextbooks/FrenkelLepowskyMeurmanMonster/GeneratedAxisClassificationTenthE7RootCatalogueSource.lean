/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitRootIndices
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! Original Golay source coordinates transport the complete existing E8 root catalogue
to the standard octad without changing its local root coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Six genuine original Golay letters map the ordered standard octad to Fifth's ordered octad. -/
def generatedTenthE7RootCataloguePermutation : golayAutomorphismSubgroup :=
  golayStabilizerAutomorphism 0 *
    golayStabilizerAutomorphism 0 *
    golayStabilizerAutomorphism 0 *
    golayStabilizerAutomorphism 0 *
    golayStabilizerAutomorphism 102 *
    golayStabilizerAutomorphism 112

/-- Complete twenty-four-coordinate data of the genuine source word. -/
def generatedTenthE7RootCatalogueForward : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 16, 17, 18, 19, 14, 13, 15, 12, 9, 11, 10, 8, 7, 6, 5, 4, 23, 22, 21, 20]

/-- Every physical coordinate of the source word equals its displayed forward value. -/
theorem generatedTenth_e7_root_catalogue_forward : ∀ i : Fin 24,
    generatedTenthE7RootCataloguePermutation.val i = generatedTenthE7RootCatalogueForward i := by
  decide +kernel

/-- Insert the unchanged eight local coordinates into the actual standard octad. -/
def generatedTenthE7RootCatalogueInsert (v : Fin 8 → ℤ) (i : Fin 24) : ℤ :=
  if h : i.val < 8 then v ⟨i.val, h⟩ else 0

/-- Original lattice root representatives transported by the actual inverse Golay word. -/
def generatedTenthE7StandardE8Root (r : Fin 120) : leechIntegral :=
  leechIntegralAction (golayPermutationIsometry generatedTenthE7RootCataloguePermutation⁻¹)
    (leechSeventhE8Root r)

/-- Every complete actual root retains all eight local coordinates and every zero coordinate. -/
theorem generatedTenth_e7_standard_e8_root_physical (r : Fin 120) :
    (generatedTenthE7StandardE8Root r).val =
      generatedTenthE7RootCatalogueInsert (leechSeventhE8RootLocal r) := by
  unfold generatedTenthE7StandardE8Root
  rw [leechIntegralAction_golayPermutation, leechSeventhE8Root_physical]
  ext i
  change generatedFifthFrameInsert (leechSeventhE8RootLocal r)
    (generatedTenthE7RootCataloguePermutation.val i) = _
  rw [generatedTenth_e7_root_catalogue_forward]
  fin_cases i <;>
    simp [generatedTenthE7RootCatalogueForward, generatedFifthFrameInsert,
      generatedTenthE7RootCatalogueInsert]

/-- Every transported representative is a genuine norm-four vector in the original lattice. -/
theorem generatedTenth_e7_standard_e8_root_square (r : Fin 120) :
    leechSquareSum (generatedTenthE7StandardE8Root r).val = 32 := by
  rw [generatedTenthE7StandardE8Root, leechIntegralAction_squareSum, leechSeventhE8Root_norm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
