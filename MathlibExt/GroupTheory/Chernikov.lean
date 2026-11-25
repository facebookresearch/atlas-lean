/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Index

/-!
# Chernikov groups

`IsChernikov` describes groups with an abelian subgroup of finite index satisfying the
descending chain condition on subgroups.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.GroupClassesShared

/-- `G` is a Chernikov group: it has an abelian subgroup of finite index satisfying the minimal
condition on subgroups. An abelian group with the minimal condition is a direct product of finitely
many quasicyclic groups and a finite group, so this is the usual definition: a finite extension of
a direct product of finitely many quasicyclic groups (finite groups are the case of no factors). -/
def IsChernikov (G : Type*) [Group G] : Prop :=
  ∃ A : Subgroup G, A.FiniteIndex ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ WellFoundedLT (Subgroup A)

end MathlibExt.GroupTheory.GroupClassesShared
