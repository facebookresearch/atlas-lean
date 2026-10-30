/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.StraightWalk`

* `sw_horizSeg_mem_support`: `(1, 0)` lies on the horizontal segment from `(0, 0)` to `(2, 0)` and
  `(3, 0)` does not; the segment from `(2, 0)` back to `(0, 0)` contains `(1, 0)`.
* `sw_horizSeg_support_nodup`, `sw_vertSeg_support_nodup`: segments are paths.
* `sw_lshape_support_eq`: the L-shaped walk from `(0, 0)` to `(2, 3)` passes through `(2, 1)`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StraightWalk

example : (![1, 0] : Site 2) ∈ (sw_horizSeg 0 0 2).support :=
  (sw_horizSeg_mem_support 0 0 2 _).2 ⟨1, by norm_num [Set.mem_uIcc], rfl⟩

example : (![1, 0] : Site 2) ∈ (sw_horizSeg 0 2 0).support :=
  (sw_horizSeg_mem_support 0 2 0 _).2 ⟨1, by norm_num [Set.mem_uIcc], rfl⟩

example : (![3, 0] : Site 2) ∉ (sw_horizSeg 0 0 2).support := by
  rw [sw_horizSeg_mem_support]
  rintro ⟨t, ht, h⟩
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero] at h0
  rw [Set.mem_uIcc] at ht
  omega

example : (sw_horizSeg 0 0 5).support.Nodup := sw_horizSeg_support_nodup 0 0 5

example : (sw_vertSeg 1 (-2) 3).support.Nodup := sw_vertSeg_support_nodup 1 (-2) 3

example : (![2, 1] : Site 2) ∈ (sw_lshape 0 0 2 3).support :=
  (sw_lshape_support_eq 0 0 2 3 _).2 (Or.inr ⟨1, by norm_num [Set.mem_uIcc], rfl⟩)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StraightWalk
