/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Rearrangement.SortingByReversals
public meta import CSLibExt.Bioinformatics.Rearrangement.SortingByReversals

/-!
# Sorting by reversals tests

Concrete breakpoint counts, doubling values, explicit sorting witnesses
(including singleton sign flips), and identity distances, for
`CSLibExt.Bioinformatics.Rearrangement.SortingByReversals`.
-/

namespace CSLibExtTest.Bioinformatics.Rearrangement

open Cslib.Bioinformatics.Rearrangement.SortingByReversals

/-- Identity has distance zero (empty). -/
example : udist 0 [] List.Perm.rfl = 0 :=
  (udist_eq_zero_iff List.Perm.rfl).mpr rfl

/-- Identity has distance zero (singleton). -/
example : udist 1 [1] List.Perm.rfl = 0 :=
  (udist_eq_zero_iff List.Perm.rfl).mpr rfl

/-- Identity has distance zero (three elements). -/
example : udist 3 [1, 2, 3] List.Perm.rfl = 0 :=
  (udist_eq_zero_iff List.Perm.rfl).mpr rfl

/-- Breakpoint count example. -/
example : ubreaks 3 [3, 1, 2] = 3 := by decide

/-- Two-element reversal distance is one. -/
example (hvalid : UValid 2 [2, 1]) : udist 2 [2, 1] hvalid = 1 := by
  have hb2 : ubreaks 2 [2, 1] = 2 := by decide
  have hle := ub_le_two_mul_udist hvalid
  rw [hb2] at hle
  have hge : 1 ≤ udist 2 [2, 1] hvalid := by omega
  have hwit : USortableIn 1 2 [2, 1] :=
    USortableIn.step 0 2 [2, 1] 0 1 (by decide) (by decide) (USortableIn.done 2)
  have hupper : udist 2 [2, 1] hvalid ≤ 1 :=
    Nat.find_min' (sortable 2 [2, 1] hvalid) hwit
  omega

#print axioms ub_le_two_mul_udist
#print axioms ubreaks_eq_zero_iff
#print axioms udist_eq_zero_iff

/-- Tests for the signed doubling correspondence. -/
example : dbl [2, 1] = [3, 4, 1, 2] := by decide
example : dbl [-2, -1] = [4, 3, 2, 1] := by decide
-- Task text lists sbreaks 2 [2,1] = 2; the directed definition gives 3
-- ([0,2,1,3] has no directed adjacency), confirmed by decide below.
example : sbreaks 2 [2, 1] = 3 := by decide
example : sbreaks 2 [2, 1] ≠ 2 := by decide
example : sbreaks 2 [-2, -1] = 2 := by decide
example : sbreaks 3 [-1, 2, 3] = 2 := by decide
example : sbreaks 6 [-6, -4, -1, 5, 2, 3]
    = ubreaks 12 (dbl [-6, -4, -1, 5, 2, 3]) := by decide
example : sbreaks 1 [1, 1] = 1 := by decide
example : ubreaks 2 (dbl [1, 1]) = 0 := by decide
example : sbreaks 1 [1, 1] ≠ ubreaks 2 (dbl [1, 1]) := by decide

#print axioms dbl_valid
#print axioms sbreaks_eq_ubreaks_dbl_of_valid
#print axioms sbreaks_eq_ubreaks_dbl_counterex

example : SSortableIn 1 1 [-1] :=
  SSortableIn.step 0 1 [-1] 0 0 (le_refl 0) (by decide) (SSortableIn.done 1)

example : SSortableIn 1 2 [-2, -1] :=
  SSortableIn.step 0 2 [-2, -1] 0 1 (by decide) (by decide) (SSortableIn.done 2)

example : SSortableIn 1 3 [-1, 2, 3] :=
  SSortableIn.step 0 3 [-1, 2, 3] 0 0 (le_refl 0) (by decide) (SSortableIn.done 3)

example : srevBlock [-2, -1] 0 1 = [1, 2] := by decide

example : dbl (srevBlock [-2, -1] 0 1) = revBlock (dbl [-2, -1]) 0 3 := by decide

example (h : SValid 0 ((List.Icc 1 0).map Int.ofNat)) : sdist 0 _ h = 0 :=
  (sdist_eq_zero_iff _ _ h).mpr rfl

example (h : SValid 1 ((List.Icc 1 1).map Int.ofNat)) : sdist 1 _ h = 0 :=
  (sdist_eq_zero_iff _ _ h).mpr rfl

example (h : SValid 3 ((List.Icc 1 3).map Int.ofNat)) : sdist 3 _ h = 0 :=
  (sdist_eq_zero_iff _ _ h).mpr rfl

#print axioms sb_le_two_mul_sdist
#print axioms sbreaks_eq_zero_iff
#print axioms dbl_srevBlock

end CSLibExtTest.Bioinformatics.Rearrangement
