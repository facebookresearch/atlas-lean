/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CollaredWalkCrossing
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.CollaredWalkCrossing`

* `collaredWalks_meet_on_original_supports` on the unit square `[0, 1]²` with the vertical crossing
  `V` from `(0, 0)` to `(0, 1)` and the horizontal crossing `H` from `(0, 0)` to `(1, 0)`: every
  hypothesis (including the four collar-meeting conditions) is discharged, so the theorem is
  nonvacuous.
* `horizontalWallExtension_mem_support_iff`: the extension of `H` to columns `0, 1` contains `(1, 0)`.
-/

@[expose] public section

open StatMech.Lattice StatMech.RSW.Box SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CollaredWalkCrossing

theorem vmono {x a b c d : ℤ} (h : Set.uIcc a b ⊆ Set.uIcc c d) {z : Site 2}
    (hz : z ∈ (sw_vertSeg x a b).support) : z ∈ (sw_vertSeg x c d).support := by
  obtain ⟨t, ht, rfl⟩ := (sw_vertSeg_mem_support _ _ _ _).1 hz
  exact (sw_vertSeg_mem_support _ _ _ _).2 ⟨t, h ht, rfl⟩

theorem hmono {y a b c d : ℤ} (h : Set.uIcc a b ⊆ Set.uIcc c d) {z : Site 2}
    (hz : z ∈ (sw_horizSeg y a b).support) : z ∈ (sw_horizSeg y c d).support := by
  obtain ⟨t, ht, rfl⟩ := (sw_horizSeg_mem_support _ _ _ _).1 hz
  exact (sw_horizSeg_mem_support _ _ _ _).2 ⟨t, h ht, rfl⟩

theorem uIcc_sub {a b : ℤ} (ha : 0 ≤ a) (ha' : a ≤ 1) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    Set.uIcc a b ⊆ Set.uIcc 0 1 :=
  Set.uIcc_subset_uIcc (by simp; omega) (by simp; omega)

example : ∃ z ∈ (sw_horizSeg 0 0 1).support, z ∈ (sw_vertSeg 0 0 1).support :=
  collaredWalks_meet_on_original_supports (alpha := 0) (beta := 1) (bottom := 0) (top := 1)
    (by norm_num) (by norm_num) (sw_vertSeg 0 0 1) (sw_horizSeg 0 0 1)
    (by simp) (by simp) (by simp) (by simp)
    (fun z hz => by
      obtain ⟨t, ht, rfl⟩ := (sw_vertSeg_mem_support _ _ _ _).1 hz
      rw [Set.mem_uIcc] at ht; simp; omega)
    (fun z hz => by
      obtain ⟨t, ht, rfl⟩ := (sw_horizSeg_mem_support _ _ _ _).1 hz
      rw [Set.mem_uIcc] at ht; simp; omega)
    (fun z _ hz => vmono (uIcc_sub (by simp) (by simp) (by simp) (by simp)) hz)
    (fun z _ hz => vmono (uIcc_sub (by simp) (by simp) (by simp) (by simp)) hz)
    (fun z _ hz => hmono (uIcc_sub (by simp) (by simp) (by simp) (by simp)) hz)
    (fun z _ hz => hmono (uIcc_sub (by simp) (by simp) (by simp) (by simp)) hz)

example : (![1, 0] : Site 2) ∈ (horizontalWallExtension 0 1 (sw_horizSeg 0 0 1)).support :=
  (horizontalWallExtension_mem_support_iff 0 1 _).2
    (Or.inr (Or.inl ((sw_horizSeg_mem_support _ _ _ _).2 ⟨1, by simp, rfl⟩)))

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.CollaredWalkCrossing
