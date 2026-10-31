/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.WalkCellBridge

import Mathlib.Tactic.Ring.RingNF

/-!
# The corner defect of the interior is a sum over walk vertices

Lattice points off the walk carry zero corner weight for the interior of a closed walk, since all
four cells around them are inside or all are outside. For a simple walk the corner defect of the
interior is therefore the sum of the corner weights at the walk vertices.

## Main results

* `StatMech.Onsager.WalkCornerSum.cornerDiff_interior_eq_walk_sum`.
-/

@[expose] public section

namespace StatMech.Onsager.WalkCornerSum

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.CellCount StatMech.Onsager.CellEuler StatMech.Onsager.JordanParity
  StatMech.Onsager.InteriorCells StatMech.Onsager.WalkCellBridge

variable {n : ℕ} [NeZero n]

/-- A lattice point off the walk has corner weight `0` for the interior. -/
theorem cornerWeight_zero_of_notMem_image (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (vx vy : ℤ) (hnv : ∀ k : Fin n, pos d k ≠ (vx, vy)) :
    cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = 0 := by
  obtain ⟨e1, e2, e3⟩ := rayParity_const_of_not_vertex d hclosed vx vy hnv
  have h4 : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ)
      = 4 * (if rayParity d vx vy = 1 then (1 : ℤ) else 0) := by
    rw [cornerCount_interior_eq, e1, e2, e3]; ring
  by_cases hr : rayParity d vx vy = 1
  · rw [hr] at h4; simp only at h4
    have : cornerCount (interiorCells d hclosed) (vx, vy) = 4 := by exact_mod_cast h4
    rw [this]; unfold cornerWeight; decide
  · rw [ite_eq_right hr] at h4
    have : cornerCount (interiorCells d hclosed) (vx, vy) = 0 := by
      have : (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = 0 := by rw [h4]; ring
      exact_mod_cast this
    rw [this]; unfold cornerWeight; decide

/-- For a simple closed walk, the corner defect of the interior is the sum of the corner weights at
  the walk vertices. -/
theorem cornerDiff_interior_eq_walk_sum (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d)) :
    cornerDiff (interiorCells d hclosed)
      = ∑ k : Fin n, cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)) := by
  have himg : ∑ v ∈ Finset.univ.image (pos d),
      cornerWeight (cornerCount (interiorCells d hclosed) v)
      = ∑ k : Fin n, cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)) :=
    Finset.sum_image (fun a _ b _ h => hsimple h)
  have h1 : ∑ v ∈ cellVerts (interiorCells d hclosed),
        cornerWeight (cornerCount (interiorCells d hclosed) v)
      = ∑ v ∈ Finset.univ.image (pos d) ∪ cellVerts (interiorCells d hclosed),
        cornerWeight (cornerCount (interiorCells d hclosed) v) :=
    Finset.sum_subset Finset.subset_union_right (by
      intro v _ hv
      have hcc : cornerCount (interiorCells d hclosed) v = 0 := by
        by_contra hne
        exact hv ((cornerCount_pos_iff_mem (interiorCells d hclosed) v).mp
          (Nat.pos_of_ne_zero hne))
      rw [hcc]; unfold cornerWeight; decide)
  have h2 : ∑ v ∈ Finset.univ.image (pos d),
        cornerWeight (cornerCount (interiorCells d hclosed) v)
      = ∑ v ∈ Finset.univ.image (pos d) ∪ cellVerts (interiorCells d hclosed),
        cornerWeight (cornerCount (interiorCells d hclosed) v) :=
    Finset.sum_subset Finset.subset_union_left (by
      intro v _ hv
      obtain ⟨vx, vy⟩ := v
      exact cornerWeight_zero_of_notMem_image d hclosed vx vy
        (fun k hk => hv (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)))
  rw [cornerDiff_eq_sum, h1, ← h2, himg]

end StatMech.Onsager.WalkCornerSum
