/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact four-coordinate data and a decreasing rank for the norm-eight reduction. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- First tetrad after applying the actual three-bases matrix to the prepared row. -/
def leechNormEightXiTargetRows : Fin 8 → Fin 4 → ℤ :=
  ![![-4, -4, -4, -4], ![0, -4, -4, -4], ![-8, 0, 0, 0], ![0, 0, -2, -6],
    ![1, -3, -3, -3], ![-4, 0, 0, 0], ![0, -2, -4, -4], ![1, -1, -1, -5]]

/-- Rank of each shape in the constructive reduction DAG. -/
def leechNormEightShapeRank : Fin 8 → ℕ := ![0, 2, 1, 3, 6, 7, 4, 5]

theorem leechNormEightXiTargetRows_double (s : Fin 8) :
    2 * leechNormEightXiTargetRows s 0 = -leechNormEightTargetRows s 0 +
      leechNormEightTargetRows s 1 + leechNormEightTargetRows s 2 + leechNormEightTargetRows s 3 ∧
    2 * leechNormEightXiTargetRows s 1 = -leechNormEightTargetRows s 0 +
      leechNormEightTargetRows s 1 - leechNormEightTargetRows s 2 - leechNormEightTargetRows s 3 ∧
    2 * leechNormEightXiTargetRows s 2 = -leechNormEightTargetRows s 0 -
      leechNormEightTargetRows s 1 + leechNormEightTargetRows s 2 - leechNormEightTargetRows s 3 ∧
    2 * leechNormEightXiTargetRows s 3 = -leechNormEightTargetRows s 0 -
      leechNormEightTargetRows s 1 - leechNormEightTargetRows s 2 +
      leechNormEightTargetRows s 3 := by
  revert s
  decide +kernel

/-- All shapes compatible with the four transformed coordinates have strictly smaller rank. -/
theorem leechNormEightXiTargetRows_rank_decreases (s t : Fin 8) (hs : s ≠ 0)
    (hc : ∀ k : Fin 9,
      (Finset.univ.filter fun j => (leechNormEightXiTargetRows s j).natAbs = k.val).card ≤
        leechNormEightShapeCounts t k) :
    leechNormEightShapeRank t < leechNormEightShapeRank s := by
  revert s t
  decide +kernel

/-- A prescribed injective row gives lower bounds on the actual coordinate multiplicities. -/
theorem leechNormEight_row_multiplicity_le (u : Fin 24 → ℤ) (row : Fin 4 → ℤ)
    (hr : ∀ j : Fin 4, u (Fin.castAdd 20 j) = row j) (k : Fin 9) :
    (Finset.univ.filter fun j => (row j).natAbs = k.val).card ≤
      leechNormEightMultiplicity u k := by
  classical
  let f : Fin 4 → Fin 24 := fun j => Fin.castAdd 20 j
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  calc
    _ = ((Finset.univ.filter fun j => (row j).natAbs = k.val).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by rw [hr j]; exact (Finset.mem_filter.mp hj).2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
