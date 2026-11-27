/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Security.AccessControl.RBAC0
import Mathlib.Data.Set.Insert

/-! # Regressions for the base role-based access-control model -/

set_option autoImplicit false

namespace Cslib.Security.AccessControl.RBAC0.Tests

private inductive Role where
  | reader | writer | unassigned
  deriving DecidableEq

private inductive Permission where
  | view | edit | restricted
  deriving DecidableEq

-- Both sessions have the same owner, but their role sets are independent.
-- Session `false` activates its writer role only in snapshot `true`.
private def exampleModel : RBAC0 Unit Role Permission Bool Bool where
  userAssignment _ r := r ≠ .unassigned
  permissionAssignment p r := match r with
    | .reader => p = .view
    | .writer => p = .edit
    | .unassigned => p = .restricted
  owner _ := ()
  activeRoles t s := if s then {.writer} else if t then {.reader, .writer} else {.reader}
  activeRoles_assigned := by
    intro t s r hr
    cases t <;> cases s <;> cases r <;> simp_all

-- The owner is assigned the writer role, but this session has not activated it yet.
example : exampleModel.userAssignment (exampleModel.owner false) .writer ∧
    Permission.edit ∉ exampleModel.permissions false false := by
  refine ⟨?_, ?_⟩
  · change Role.writer ≠ Role.unassigned
    decide
  · rintro ⟨r, hr, hp⟩
    have he : r = Role.reader := hr
    subst r
    cases hp

-- Another session of the same owner has the permission at the same snapshot.
example : Permission.edit ∈ exampleModel.permissions false true :=
  ⟨.writer, rfl, rfl⟩

-- The two-role session receives a distinct permission from each active role.
example : Permission.view ∈ exampleModel.permissions true false ∧
    Permission.edit ∈ exampleModel.permissions true false := by
  refine ⟨?_, ?_⟩
  · exact ⟨.reader, by simp [exampleModel], rfl⟩
  · exact ⟨.writer, by simp [exampleModel], rfl⟩

-- A grant from a role the owner was never assigned cannot enter the session.
example : Permission.restricted ∉ exampleModel.permissions true false := by
  intro h
  obtain ⟨r, ha, hg⟩ := exampleModel.exists_assigned_role_of_mem_permissions h
  cases r with
  | reader => cases hg
  | writer => cases hg
  | unassigned => exact ha rfl

end Cslib.Security.AccessControl.RBAC0.Tests
