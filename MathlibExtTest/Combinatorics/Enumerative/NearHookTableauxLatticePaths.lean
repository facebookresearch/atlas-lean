/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NearHookTableauxLatticePaths
import Mathlib.Order.Interval.Finset.Nat

open MetaMathlibExt

-- Rows [1, 2, 5], [3, 4], [6]. The heart is 4 and its predecessor is in the leg.
private def sixCells : SemistandardYoungTableau (nearHookTheta 1) where
  entry i j := if (i, j) ∈ nearHookTheta 1 then 1 + 2 * i + j + 2 * (j - 1) + (i - 1) else 0
  row_weak' := by
    intro i j k hj hc
    simp only [hc, (nearHookTheta 1).up_left_mem le_rfl hj.le hc, ite_true]
    omega
  col_strict' := by
    intro i k j hi hc
    simp only [hc, (nearHookTheta 1).up_left_mem hi.le le_rfl hc, ite_true]
    omega
  zeros' := by simp_all

example : nearHookTableauToPathXi 1 sixCells = [(1, 0), (-1, 0), (1, 0), (0, 1)] := by
  decide

example : nearHookTableauToPathXi 1 sixCells ∈ firstQuadrantPaths 1 := by
  apply (bijOn_nearHookTableauToPathXi 1).mapsTo
  change Set.BijOn _ _ (Set.Icc 1 6)
  rw [← Finset.coe_Icc]
  apply (Finset.image_eq_iff_bijOn_of_card (by decide)).mp
  decide

-- For the empty arm and leg extensions, the north-south walk has a unique preimage.
example : ∃! T : SemistandardYoungTableau (nearHookTheta 0),
    Set.BijOn (fun c : ℕ × ℕ => T c.1 c.2) (nearHookTheta 0).cells (Set.Icc 1 4) ∧
      nearHookTableauToPathXi 0 T = [(0, 1), (0, -1)] := by
  have hb := bijOn_nearHookTableauToPathXi 0
  obtain ⟨T, hT, hpath⟩ := hb.surjOn north_south_mem_firstQuadrantPaths_zero
  exact ⟨T, ⟨hT, hpath⟩, fun U hU => hb.injOn hU.1 hT (hU.2.trans hpath.symm)⟩
