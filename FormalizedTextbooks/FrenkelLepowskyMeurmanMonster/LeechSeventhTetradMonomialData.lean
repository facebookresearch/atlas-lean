/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradClasses

/-! Moving the one negative entry within a genuine tetrad does not change its lattice class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The four actual tetrad coordinates, with an optional negative entry at a specified position. -/
def leechSeventhTetradAtCoefficients (t k : Fin 24) (b : Bool) (i : Fin 24) : ℤ :=
  (if i ∈ generatedSeventhFiveFrameCoordinates ∧ i ≠ t then 1 else 0) -
    (if b then 2 * (Pi.single k 1 : Fin 24 → ℤ) i else 0)

set_option maxHeartbeats 0 in
-- Only the literal five positions and two sign choices enter this finite check.
/-- Every stated tetrad with at most one negative entry has even integral sum. -/
theorem leechSeventhTetradAt_even_sum : ∀ t k : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates →
      k ∈ generatedSeventhFiveFrameCoordinates → k ≠ t → ∀ b : Bool,
        Even (∑ i, leechSeventhTetradAtCoefficients t k b i) := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradAtCoefficients
  decide +kernel

/-- Every stated single-negative tetrad is an element of the actual Leech lattice. -/
def leechSeventhTetradAtLattice (t : {i // i ∈ generatedSeventhFiveFrameCoordinates})
    (k : Fin 24) (hk : k ∈ generatedSeventhFiveFrameCoordinates) (hkt : k ≠ t.val)
    (b : Bool) : leechIntegral :=
  ⟨(4 : ℤ) • leechSeventhTetradAtCoefficients t.val k b,
    (leechSeventh_four_coordinate_mem_iff _).mpr
      (leechSeventhTetradAt_even_sum t.val k t.property hk hkt b)⟩

set_option maxHeartbeats 0 in
-- Check the actual signed coefficients at all finite coordinate positions.
private theorem coefficient_difference : ∀ t k : Fin 24,
    t ∈ generatedSeventhFiveFrameCoordinates →
      k ∈ generatedSeventhFiveFrameCoordinates → k ≠ t → ∀ b : Bool,
        leechSeventhTetradAtCoefficients t k b - leechSeventhTetradCoefficients t b =
          (2 : ℤ) • (if b then
            (-Pi.single k 1 + Pi.single (leechSeventhTetradNegativeCoordinate t) 1 :
              Fin 24 → ℤ) else 0) := by
  unfold generatedSeventhFiveFrameCoordinates leechSeventhTetradAtCoefficients
    leechSeventhTetradCoefficients leechSeventhTetradNegativeCoordinate
  decide +kernel

/-- Any position for the one negative coordinate gives the same genuine tetrad sign class. -/
theorem leechSeventhTetradAt_class (t : {i // i ∈ generatedSeventhFiveFrameCoordinates})
    (k : Fin 24) (hk : k ∈ generatedSeventhFiveFrameCoordinates) (hkt : k ≠ t.val)
    (b : Bool) :
    leechReduction (leechSeventhTetradAtLattice t k hk hkt b) =
      leechSeventhTetradClass (t, b) := by
  let w : Fin 24 → ℤ := if b then
    -Pi.single k 1 + Pi.single (leechSeventhTetradNegativeCoordinate t.val) 1 else 0
  have hd : (leechSeventhTetradAtLattice t k hk hkt b).val -
      (leechSeventhTetradLattice t b).val = (2 : ℤ) • ((4 : ℤ) • w) := by
    change (4 : ℤ) • leechSeventhTetradAtCoefficients t.val k b -
      (4 : ℤ) • leechSeventhTetradCoefficients t.val b = _
    rw [← smul_sub, coefficient_difference t.val k t.property hk hkt b]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  apply (leechSeventh_reduction_eq_iff_half _ _ _ hd).mpr
  apply (leechSeventh_four_coordinate_mem_iff w).mpr
  have hs : ∑ i, w i = 0 := by
    cases b <;> simp [w, Finset.sum_add_distrib, Finset.sum_neg_distrib, Pi.single_apply]
  rw [hs]
  exact ⟨0, by norm_num⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
