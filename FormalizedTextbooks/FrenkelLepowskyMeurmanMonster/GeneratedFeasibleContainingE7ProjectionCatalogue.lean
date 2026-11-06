/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOutgoingCoefficientCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitReachability
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootCatalogueSection

/-! Genuine doubled section projections of the original selected-square-eight short vectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The original Golay codeword 2063 defines the genuine sign on the entire source section. -/
def generatedFeasibleContainingSectionSign : leechIsomSubgroup :=
  golaySignIsometry ⟨golayStandardOctad, golayStandardOctad_mem⟩

/-- Twice the source-section projection is an actual lattice vector, as a difference of two
actual lattice vectors under the original Golay sign isometry. -/
def generatedFeasibleContainingDoubledProjection (u : leechIntegral) : leechIntegral :=
  u - leechIntegralAction generatedFeasibleContainingSectionSign u

/-- Every original coordinate of the actual difference is twice the selected coordinate. -/
theorem generatedFeasibleContainingDoubledProjection_coordinate (u : leechIntegral)
    (i : Fin 24) :
    (generatedFeasibleContainingDoubledProjection u).val i =
      if i.val < 8 then 2 * u.val i else 0 := by
  unfold generatedFeasibleContainingDoubledProjection generatedFeasibleContainingSectionSign
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [leechIntegralAction_golaySign]
  change u.val i - golayIntegerSign golayStandardOctad u.val i = _
  by_cases hi : i.val < 8
  · simp [golayIntegerSign, golayStandardOctad, hi]
    ring
  · simp [golayIntegerSign, golayStandardOctad, hi]

/-- The entire doubled projection has exactly four times the original selected square. -/
theorem generatedFeasibleContainingDoubledProjection_square (u : leechIntegral) :
    leechSquareSum (generatedFeasibleContainingDoubledProjection u).val =
      4 * generatedFeasibleContainingSelectedSquare
        (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) u.val := by
  rw [generatedFeasibleContaining_selected_source_word]
  unfold leechSquareSum generatedFeasibleContainingSelectedSquare
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [generatedFeasibleContainingDoubledProjection_coordinate]
  by_cases hi : i.val < 8
  · have hc : golayStandardOctad i = 1 := by simp [golayStandardOctad, hi]
    rw [ite_eq_left hi, hc]
    rw [show ((1 : ZMod 2).val : ℤ) = 1 from by decide +kernel]
    ring
  · have hc : golayStandardOctad i = 0 := by simp [golayStandardOctad, hi]
    rw [ite_eq_right hi, hc]
    simp

/-- The actual doubled projection lies in the entire original coordinate E8 section. -/
theorem generatedFeasibleContainingDoubledProjection_section (u : leechIntegral) :
    generatedFeasibleContainingDoubledProjection u ∈
      generatedAxisE8CoordinateSection golayStandardOctad := by
  intro i hi
  rw [generatedFeasibleContainingDoubledProjection_coordinate]
  have hn : ¬ i.val < 8 := by
    intro hl
    simp [golayStandardOctad, hl] at hi
  exact ite_eq_right hn

/-- The actual preferred root perpendicularity is preserved in the doubled source projection. -/
theorem generatedFeasibleContainingDoubledProjection_orthogonal (u : leechIntegral)
    (hu : u.val 0 = u.val 1) :
    (generatedFeasibleContainingDoubledProjection u).val 0 =
      (generatedFeasibleContainingDoubledProjection u).val 1 := by
  rw [generatedFeasibleContainingDoubledProjection_coordinate,
    generatedFeasibleContainingDoubledProjection_coordinate]
  norm_num
  rw [hu]

/-- Every entire original selected-eight short vector projects to an actual norm-four root,
with one of the two genuine integral orientations. -/
theorem generatedFeasibleContaining_selected_eight_projected_root (r : GriessShortIndex)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 8) :
    ∃ s : GriessShortIndex,
      generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r) =
          griessShortLatticeVector s ∨
        generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r) =
          -griessShortLatticeVector s := by
  have hn := generatedFeasibleContainingDoubledProjection_square (griessShortLatticeVector r)
  change leechSquareSum _ = 4 * generatedFeasibleContainingSelectedShortSquare r at hn
  rw [hr] at hn
  norm_num at hn
  obtain ⟨s, hs⟩ := leechShort_catalog _ hn
  refine ⟨s, ?_⟩
  rcases hs with hs | hs
  · exact Or.inl (Subtype.ext hs)
  · exact Or.inr (Subtype.ext hs)

/-- The entire actual source perpendicular preferred-root catalogue, with its original coordinates.
-/
def generatedFeasibleContainingE7ProjectionRootLines :=
  {r : generatedAxisE8ShortLines (generatedAxisE8CoordinateSection golayStandardOctad) //
    griessShortIntegral r.val 0 = griessShortIntegral r.val 1}

/-- Each original perpendicular selected-eight short vector has an actual preferred projection
line in the complete source E7 catalogue. -/
theorem generatedFeasibleContaining_selected_eight_projected_line
    (r : GriessShortIndex) (hr : generatedFeasibleContainingSelectedShortSquare r = 8)
    (ho : griessShortIntegral r 0 = griessShortIntegral r 1) :
    ∃ s : generatedFeasibleContainingE7ProjectionRootLines,
      generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r) =
          griessShortLatticeVector s.val.val ∨
        generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r) =
          -griessShortLatticeVector s.val.val := by
  obtain ⟨s, hs⟩ := generatedFeasibleContaining_selected_eight_projected_root r hr
  have hsection := generatedFeasibleContainingDoubledProjection_section (griessShortLatticeVector r)
  have horth := generatedFeasibleContainingDoubledProjection_orthogonal
    (griessShortLatticeVector r) ho
  have hm : griessShortLatticeVector s ∈
      generatedAxisE8CoordinateSection golayStandardOctad := by
    rcases hs with hs | hs
    · rwa [hs] at hsection
    · rw [hs] at hsection
      exact (Submodule.neg_mem_iff _).mp hsection
  have hp : griessShortIntegral s 0 = griessShortIntegral s 1 := by
    rcases hs with hs | hs
    · rw [hs] at horth
      exact horth
    · rw [hs] at horth
      change -griessShortIntegral s 0 = -griessShortIntegral s 1 at horth
      exact neg_injective horth
  exact ⟨⟨⟨s, hm⟩, hp⟩, hs⟩

private theorem selected_full_supported (c : Fin 24 → ZMod 2) (u : leechIntegral)
    (hS : generatedFeasibleContainingSelectedSquare c u.val = leechSquareSum u.val) :
    generatedOctadSupported c u.val := by
  have hn (i : Fin 24) :
      0 ≤ u.val i ^ 2 - ((c i).val : ℤ) * u.val i ^ 2 := by
    have hc : ((c i).val : ℤ) ≤ 1 := by have h := (c i).val_lt; omega
    have h := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (u.val i))
    nlinarith
  have hz : (∑ i : Fin 24, (u.val i ^ 2 - ((c i).val : ℤ) * u.val i ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change leechSquareSum u.val - generatedFeasibleContainingSelectedSquare c u.val = 0
    rw [hS, sub_self]
  intro i hi
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hz i
    (Finset.mem_univ i)
  rw [hi] at ht
  norm_num at ht
  nlinarith

private theorem supported_selected_full (c : Fin 24 → ZMod 2) (u : leechIntegral)
    (hu : generatedOctadSupported c u.val) :
    generatedFeasibleContainingSelectedSquare c u.val = leechSquareSum u.val := by
  unfold generatedFeasibleContainingSelectedSquare leechSquareSum
  apply Finset.sum_congr rfl
  intro i _
  have hc : (c i).val = 0 ∨ (c i).val = 1 := by have h := (c i).val_lt; omega
  rcases hc with hc | hc
  · have hz := hu i ((ZMod.val_eq_zero _).mp hc)
    simp [hc, hz]
  · simp [hc]

/-- The entire source E8 short-line set is exactly the full selected-square-thirty-two bin. -/
theorem generatedFeasibleContaining_selected_full_short_iff (r : GriessShortIndex) :
    generatedFeasibleContainingSelectedShortSquare r = 32 ↔
      r ∈ generatedAxisE8ShortLines (generatedAxisE8CoordinateSection golayStandardOctad) := by
  change generatedFeasibleContainingSelectedSquare
    (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex) (griessShortIntegral r) =
      32 ↔ generatedOctadSupported golayStandardOctad (griessShortIntegral r)
  rw [generatedFeasibleContaining_selected_source_word]
  constructor
  · intro hs
    exact selected_full_supported golayStandardOctad (griessShortLatticeVector r)
      (hs.trans (griessShortIntegral_squareSum r).symm)
  · intro hs
    exact (supported_selected_full golayStandardOctad (griessShortLatticeVector r) hs).trans
      (griessShortIntegral_squareSum r)

/-- The complete source perpendicular root lines biject with the entire original preferred
selected-square-thirty-two catalogue. -/
def generatedFeasibleContainingE7ProjectionRootLinesEquiv :
    generatedFeasibleContainingE7ProjectionRootLines ≃
      generatedFeasibleContainingSelectedShortLabels 3 where
  toFun r := ⟨r.val.val, Finset.mem_filter.mpr
    ⟨(generatedFeasibleOrthogonalShortLabels_mem _).mpr r.property,
      (generatedFeasibleContaining_selected_full_short_iff _).mpr r.val.property⟩⟩
  invFun r := ⟨⟨r.val, (generatedFeasibleContaining_selected_full_short_iff _).mp
    (Finset.mem_filter.mp r.property).2⟩,
      (generatedFeasibleOrthogonalShortLabels_mem _).mp (Finset.mem_filter.mp r.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly sixty-three genuine preferred source root lines comprise the complete E7 catalogue. -/
theorem generatedFeasibleContainingE7ProjectionRootLines_card :
    Nat.card generatedFeasibleContainingE7ProjectionRootLines = 63 := by
  rw [Nat.card_congr generatedFeasibleContainingE7ProjectionRootLinesEquiv,
    Nat.card_eq_fintype_card, Fintype.card_coe,
    generatedFeasibleContainingSelectedShortLabels_card]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
