/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared group classes for Kourovka Notebook WantedExt statements

Definitions used by more than one `WantedExt` module of resolved Kourovka Notebook problems:
generalized quaternion groups (Problems 4.75, 7.15). Mathlib and MathlibExt have no such predicate
(checked 2026-10-23; Mathlib's `QuaternionGroup n` is the group itself, not a predicate). Fully
invariant subgroups, which describe varieties of groups through their laws (Problems 6.14-6.17,
7.24, 8.18, 8.22, 8.26), use `IsFullyInvariant` of the Kourovka 3.53 entry; conjugacy separable
groups (Problems 8.69, 8.70, 8.71, 9.2) use `IsConjugacySeparable` of `KourovkaNotebookShared`;
locally normal groups use `IsLocallyNormal` of the Kourovka 1.9 entry.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

@[expose] public section

namespace MathlibExt.GroupTheory.GroupClassesShared

/-- `P` is a generalized quaternion group: `P ≅ Q_(2^(k+2))` (`QuaternionGroup (2 ^ k)`, of order
`2 ^ (k + 2) ≥ 8`) for some `k ≥ 1`. -/
def IsGeneralizedQuaternion (P : Type*) [Group P] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ Nonempty (P ≃* QuaternionGroup (2 ^ k))

end MathlibExt.GroupTheory.GroupClassesShared
