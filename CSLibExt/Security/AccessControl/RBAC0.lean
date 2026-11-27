/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic

/-!
# The RBAC₀ model of role-based access control

User-to-role and permission-to-role assignments are many-to-many. A session has a fixed owner
and a set of active roles that can vary between snapshots. At each snapshot those roles must
be assigned to the owner. The session has exactly the permissions of its active roles, not
all the owner's assigned roles. Permission symbols have no interpretation in this model.

Source: Sandhu, Coyne, Feinstein, and Youman, *Role-Based Access Control Models*, IEEE Computer
29(2), 38–47 (1996), §4.1, Definition 1. There is no role hierarchy or lifecycle semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Security.AccessControl

/-- **Base role-based access control.** The types are the universes of users, roles, permission
symbols, sessions, and snapshots. Session ownership is independent of the snapshot. Only roles
assigned to the owner may be active in a session. -/
structure RBAC0 (User Role Permission Session Snapshot : Type*) where
  /-- User-to-role assignment, in the order `(user, role)`. -/
  userAssignment : User → Role → Prop
  /-- Permission-to-role assignment, in the order `(permission, role)`. -/
  permissionAssignment : Permission → Role → Prop
  /-- The user owning each session throughout its lifetime. -/
  owner : Session → User
  /-- The roles activated in a session at the given snapshot. -/
  activeRoles : Snapshot → Session → Set Role
  /-- Every active role is assigned to the session's owner. -/
  activeRoles_assigned : ∀ t s r, r ∈ activeRoles t s → userAssignment (owner s) r

namespace RBAC0

variable {User Role Permission Session Snapshot : Type*}

/-- The union of the permission sets of the roles active in this session at this snapshot. -/
def permissions (model : RBAC0 User Role Permission Session Snapshot)
    (t : Snapshot) (s : Session) : Set Permission :=
  {p | ∃ r ∈ model.activeRoles t s, model.permissionAssignment p r}

/-- A session permission comes from a role assigned to its owner. Assignment alone does not
imply that the role is active or that its permissions are present in this session. -/
theorem exists_assigned_role_of_mem_permissions
    (model : RBAC0 User Role Permission Session Snapshot) {t : Snapshot} {s : Session}
    {p : Permission} (hp : p ∈ model.permissions t s) :
    ∃ r, model.userAssignment (model.owner s) r ∧ model.permissionAssignment p r := by
  obtain ⟨r, hr, hp⟩ := hp
  exact ⟨r, model.activeRoles_assigned t s r hr, hp⟩

/-- Enlarging the active role set cannot remove permissions. -/
theorem permissions_mono (model : RBAC0 User Role Permission Session Snapshot)
    {t t' : Snapshot} {s s' : Session} (h : model.activeRoles t s ⊆ model.activeRoles t' s') :
    model.permissions t s ⊆ model.permissions t' s' := by
  rintro p ⟨r, hr, hp⟩
  exact ⟨r, h hr, hp⟩

/-- A session with no active roles has no permissions, regardless of its owner's assignments. -/
theorem permissions_eq_empty (model : RBAC0 User Role Permission Session Snapshot)
    {t : Snapshot} {s : Session} (h : model.activeRoles t s = ∅) : model.permissions t s = ∅ := by
  ext p
  simp only [permissions, Set.mem_ofPred_eq, h, Set.mem_empty_iff_false, false_and, exists_false]

end RBAC0

end Cslib.Security.AccessControl
