/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.PiCalculus.Scoping

/-!
# Polarized endpoint identity

Roles are linear capabilities, not additional runtime channel names.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- Opposite capabilities on a single physical π name. -/
inductive Role where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- One endpoint key consists of the existing physical name and a role. -/
structure Key where
  name : PiCalculus.Name
  role : Role
  deriving DecidableEq, Repr

/-- Reverse the linear role without changing the physical name. -/
def Role.opposite : Role → Role
  | .positive => .negative
  | .negative => .positive

/-- Role reversal is an involution. -/
@[simp] theorem Role.opposite_opposite (r : Role) :
    r.opposite.opposite = r := by
  cases r <;> rfl

/-- The peer role on the same physical channel. -/
def Key.opposite (e : Key) : Key := ⟨e.name, e.role.opposite⟩

/-- Reversing an endpoint twice recovers its entire key. -/
@[simp] theorem Key.opposite_opposite (e : Key) :
    e.opposite.opposite = e := by
  cases e
  simp [opposite]

/-- Opposite roles cannot collide, even on one physical name. -/
theorem Key.opposite_ne (e : Key) : e.opposite ≠ e := by
  rcases e with ⟨n, r⟩
  cases r <;> simp [opposite, Role.opposite]

/-- Apply an existing-name transformation, leaving the role untouched. -/
def Key.mapName (f : PiCalculus.Name → PiCalculus.Name) (e : Key) : Key :=
  ⟨f e.name, e.role⟩

/-- Injective physical-name transformations preserve endpoint identity. -/
theorem Key.mapName_injective {f : PiCalculus.Name → PiCalculus.Name}
    (hf : Function.Injective f) : Function.Injective (mapName f) := by
  rintro ⟨a, r⟩ ⟨b, s⟩ h
  simp only [mapName, Key.mk.injEq] at h ⊢
  exact ⟨hf h.1, h.2⟩

/-- Endpoint identity is exactly its physical name and linear role. -/
@[ext] theorem Key.ext {e d : Key} (hn : e.name = d.name) (hr : e.role = d.role) :
    e = d := by
  cases e
  cases d
  simp_all

/-- Distinct keys on one physical name must be opposite endpoint roles. -/
theorem Key.eq_opposite_of_name_eq {e d : Key} (hn : e.name = d.name)
    (he : e ≠ d) : d = e.opposite := by
  rcases e with ⟨a, r⟩
  rcases d with ⟨b, s⟩
  dsimp at hn
  subst b
  cases r <;> cases s <;> simp_all [opposite, Role.opposite]

end Cslib.SessionTypes.Endpoint
