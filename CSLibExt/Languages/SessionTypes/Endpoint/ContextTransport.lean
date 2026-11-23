/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Context
public import CSLibExt.Languages.SessionTypes.Endpoint.NameTransport

/-!
# Binder transport of finite ownership maps

All physical-name operations are the canonical π transformations. Context
rekeying records their effect on roles without copying name scoping.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Insert an ambient name binder at any cutoff in an ownership context. -/
def Context.lift (k : Nat) (Δ : Context) : Context :=
  rekey (Key.mapName (liftName k)) Δ
    (fun _ _ _ _ h => Key.mapName_injective (liftName_injective k) h)

set_option backward.isDefEq.respectTransparency false in
/-- Lifting keeps the entire capability at the corresponding lifted key. -/
theorem Context.lookup_lift {k : Nat} {Δ : Context} {e : Key}
    {c : Capability} :
    (lift k Δ).lookup (Key.mapName (liftName k) e) = some c ↔
      Δ.lookup e = some c := by
  rw [lift, lookup_rekey]
  constructor
  · rintro ⟨d, hd, he⟩
    have h : d = e := Key.mapName_injective (liftName_injective k) he
    subst d
    exact hd
  · intro he
    exact ⟨e, he, rfl⟩

/-- A restriction binds one physical name and creates its two distinct
linear roles. Lifted outer keys cannot be overwritten by these insertions. -/
def Context.bind (c : Capability) (Δ : Context) : Context :=
  (lift 0 Δ).insert ⟨.var 0, .positive⟩ c |>
    Finmap.insert ⟨.var 0, .negative⟩ c.dual

set_option backward.isDefEq.respectTransparency false in
/-- Both roles of the newly inserted name are fresh for the lifted context. -/
theorem Context.fresh_lift (Δ : Context) (r : Role) :
    (⟨.var 0, r⟩ : Key) ∉ lift 0 Δ := by
  intro h
  obtain ⟨e, _, he⟩ := mem_rekey.mp h
  have hn := congrArg Key.name he
  exact liftName_zero_ne_var_zero e.name hn

/-- Restriction installs the positive capability without losing it to the
opposite role's insertion. -/
theorem Context.lookup_bind_positive (c : Capability) (Δ : Context) :
    (bind c Δ).lookup ⟨.var 0, .positive⟩ = some c := by
  simp [bind]

/-- The same restriction installs the negative peer at the SAME name. -/
theorem Context.lookup_bind_negative (c : Capability) (Δ : Context) :
    (bind c Δ).lookup ⟨.var 0, .negative⟩ = some c.dual := by
  simp [bind]

/-- Lifting a single capability shifts its name, not its protocol or role. -/
theorem Context.lift_singleton (k : Nat) (e : Key) (c : Capability) :
    lift k (Finmap.singleton e c) =
      Finmap.singleton (Key.mapName (liftName k) e) c := by
  apply Finmap.ext
  rfl

/-- Inserting a binder does not manufacture an outer capability. -/
@[simp] theorem Context.lift_empty (k : Nat) : lift k (∅ : Context) = ∅ := by
  apply Finmap.ext
  rfl

/-- In an empty outer context, restriction exposes exactly its two peers. -/
theorem Context.bind_empty (c : Capability) : bind c ∅ =
    Finmap.singleton ⟨.var 0, .positive⟩ c ∪
      Finmap.singleton ⟨.var 0, .negative⟩ c.dual := by
  rw [bind, lift_empty]
  change (Finmap.singleton (⟨.var 0, .positive⟩ : Key) c : Context).insert
    ⟨.var 0, .negative⟩ c.dual = _
  have hi := Finmap.insert_union (s₁ := (∅ : Context))
    (s₂ := Finmap.singleton ⟨.var 0, .positive⟩ c)
    (a := (⟨.var 0, .negative⟩ : Key)) (b := c.dual)
  rw [Finmap.empty_union] at hi
  rw [hi]
  change (Finmap.singleton (⟨.var 0, .negative⟩ : Key) c.dual : Context) ∪
    Finmap.singleton ⟨.var 0, .positive⟩ c = _
  apply Finmap.union_comm_of_disjoint
  simp [Finmap.Disjoint, Finmap.mem_singleton]

/-- The exact restriction context has two fresh entries plus all shifted
outer ownership. No old entry is overwritten by a new endpoint role. -/
theorem Context.entries_bind (c : Capability) (Δ : Context) :
    (bind c Δ).entries =
      ⟨⟨.var 0, .negative⟩, c.dual⟩ ::ₘ
        ⟨⟨.var 0, .positive⟩, c⟩ ::ₘ (lift 0 Δ).entries := by
  rw [bind, Finmap.entries_insert_of_notMem (by
    simp [Finmap.mem_insert, fresh_lift])]
  rw [Finmap.entries_insert_of_notMem (fresh_lift Δ .positive)]

/-- Lifting preserves absence of an outer role from its finite context. -/
theorem Context.fresh_lift_of_fresh {Δ : Context} {e : Key} (he : e ∉ Δ) :
    Key.mapName (liftName 0) e ∉ Context.lift 0 Δ := by
  intro hm
  obtain ⟨d, hd, hde⟩ := Context.mem_rekey.mp hm
  have h : d = e := Key.mapName_injective (liftName_injective 0) hde
  exact he (h ▸ hd)

/-- An absent outer key remains absent after adding the fresh bound dual pair. -/
theorem Context.fresh_bind_of_fresh {Δ : Context} {e : Key} {c : Capability}
    (he : e ∉ Δ) :
    Key.mapName (liftName 0) e ∉ Context.bind c Δ := by
  intro hm
  rw [Context.bind] at hm
  rcases Finmap.mem_insert.mp hm with hm | hm
  · exact Key.lift_ne_bound e .negative hm
  · rcases Finmap.mem_insert.mp hm with hm | hm
    · exact Key.lift_ne_bound e .positive hm
    · exact Context.fresh_lift_of_fresh he hm

end Cslib.SessionTypes.Endpoint
