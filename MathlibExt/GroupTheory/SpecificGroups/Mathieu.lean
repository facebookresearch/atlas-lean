/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# The Mathieu group on 23 points

The two permutations below are the standard degree-23 generators of `M23`, as used by
GAP 4.15.1's `MathieuGroup(23)`. The conventional labels 1 through 23 are shifted to `Fin 23`.
-/

@[expose] public section

namespace MathieuGroup

/-- The 23-cycle in the standard permutation construction of `M23`. -/
def m23Cycle : Equiv.Perm (Fin 23) :=
  (List.finRange 23).formPerm

/-- The four disjoint 5-cycles in the standard permutation construction of `M23`. -/
def m23FiveCycles : Equiv.Perm (Fin 23) :=
  ([2, 16, 9, 6, 8] : List (Fin 23)).formPerm *
    ([3, 12, 13, 18, 4] : List (Fin 23)).formPerm *
    ([7, 17, 10, 11, 22] : List (Fin 23)).formPerm *
    ([14, 19, 21, 20, 15] : List (Fin 23)).formPerm

/-- The Mathieu group `M23`, as its standard subgroup of permutations of 23 points. -/
def M23 : Subgroup (Equiv.Perm (Fin 23)) :=
  Subgroup.closure {m23Cycle, m23FiveCycles}

/-- A subgroup contains `M23` exactly when it contains the two standard generators. -/
theorem m23_le_iff (H : Subgroup (Equiv.Perm (Fin 23))) :
    M23 ≤ H ↔ m23Cycle ∈ H ∧ m23FiveCycles ∈ H := by
  simp [M23, Subgroup.closure_le, Set.insert_subset_iff]

end MathieuGroup
