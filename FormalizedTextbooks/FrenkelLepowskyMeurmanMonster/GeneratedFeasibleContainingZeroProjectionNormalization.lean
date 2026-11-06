/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingE7ProjectionCatalogue

/-! Actual zero projections onto the entire containing source section. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Selected square zero means the actual lattice projection is zero. -/
theorem generatedFeasibleContaining_selected_zero_projection
    (r : GriessShortIndex)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 0) :
    generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r) = 0 := by
  have hn := generatedFeasibleContainingDoubledProjection_square (griessShortLatticeVector r)
  change leechSquareSum _ = 4 * generatedFeasibleContainingSelectedShortSquare r at hn
  rw [hr, mul_zero] at hn
  apply Subtype.ext
  funext i
  have hb := Finset.single_le_sum
    (fun j _ => sq_nonneg
      ((generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)).val j))
    (Finset.mem_univ i)
  change (∑ j : Fin 24,
    (generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)).val j ^ 2) = 0 at hn
  rw [hn] at hb
  change (generatedFeasibleContainingDoubledProjection (griessShortLatticeVector r)).val i = 0
  nlinarith

/-- All eight actual source coordinates of a zero input vanish individually. -/
theorem generatedFeasibleContaining_selected_zero_coordinates
    (r : GriessShortIndex)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 0)
    (i : Fin 24) (hi : i.val < 8) : griessShortIntegral r i = 0 := by
  have h := congrArg (fun u : leechIntegral => u.val i)
    (generatedFeasibleContaining_selected_zero_projection r hr)
  rw [generatedFeasibleContainingDoubledProjection_coordinate, ite_eq_left hi] at h
  change 2 * griessShortIntegral r i = 0 at h
  omega

/-- Zero inputs are perpendicular to the entire actual source E8 section. -/
theorem generatedFeasibleContaining_selected_zero_section_orthogonal
    (r : GriessShortIndex)
    (hr : generatedFeasibleContainingSelectedShortSquare r = 0)
    (u : leechIntegral)
    (hu : u ∈ generatedAxisE8CoordinateSection
      (golayOctadWord generatedFeasibleContainingOctadPrototypeIndex)) :
    leechIntegralPairing (griessShortIntegral r) u.val = 0 := by
  rw [generatedFeasibleContaining_selected_source_word] at hu
  unfold leechIntegralPairing
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < 8
  · rw [generatedFeasibleContaining_selected_zero_coordinates r hr i hi, zero_mul]
  · rw [hu i (by simp [golayStandardOctad, hi]), mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
