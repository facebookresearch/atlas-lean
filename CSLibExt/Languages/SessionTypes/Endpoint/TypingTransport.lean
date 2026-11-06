/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra
public import CSLibExt.Languages.SessionTypes.Endpoint.Renaming
public import CSLibExt.Languages.SessionTypes.Endpoint.Typing

/-!
# Capture-safe finite ownership transport

Renaming may be injective only on the owned domain. The input substitution
case must derive that condition from the sender/receiver linear split.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Binder extension commutes with lifting on endpoint keys.**
Entering a binder commutes with endpoint rekeying and retains its role. -/
theorem Key.under_lift (f : Name → Name) (e : Key) :
    mapName (under f) (mapName (liftName 0) e) =
      mapName (liftName 0) (mapName f e) := by
  cases e
  simp [mapName, under_lift_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **Injectivity of rekeying passes under a binder.**
Collision freedom of owned keys is stable when entering a binder. -/
theorem Context.injOn_under_lift {f : Name → Name} {Δ : Context}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    Set.InjOn (Key.mapName (under f)) {e | e ∈ Context.lift 0 Δ} := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Context.mem_rekey.mp hx
  obtain ⟨b, hb, rfl⟩ := Context.mem_rekey.mp hy
  rw [Key.under_lift, Key.under_lift] at hxy
  have he := Key.mapName_injective (liftName_injective 0) hxy
  have hab : a = b := hf ha hb he
  rw [hab]

/-- **Rekeying under a binder is the lift of the outer rekeying.**
Rekeying under a binder is exactly the lift of the outer rekeying. -/
theorem Context.rekey_under_lift {f : Name → Name} {Δ : Context}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ})
    (hu : Set.InjOn (Key.mapName (under f)) {e | e ∈ Context.lift 0 Δ}) :
    rekey (Key.mapName (under f)) (Context.lift 0 Δ) hu =
      Context.lift 0 (rekey (Key.mapName f) Δ hf) := by
  apply Finmap.ext
  simp only [Context.lift, rekey, Multiset.map_map]
  apply Multiset.map_congr rfl
  rintro ⟨e, c⟩ _
  simp [Key.under_lift]

/-- **Binder extension fixes the fresh binder's endpoint keys.**
The fresh binder's endpoint roles are fixed under name transformation. -/
theorem Key.under_fixed (f : Name → Name) (e : Key) (he : e.name = .var 0) :
    mapName (under f) e = e := by
  rcases e with ⟨a, r⟩
  change a = .var 0 at he
  subst a
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Rekeying under a binder is injective on fresh and lifted keys.**
Rekeying under a binder is injective on both fresh roles and all lifted
outer ownership, not just on endpoint keys with different physical names. -/
theorem Context.injOn_under_binder {f : Name → Name} {Δ : Context}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    Set.InjOn (Key.mapName (under f))
      {e | e.name = .var 0 ∨ e ∈ Context.lift 0 Δ} := by
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rwa [Key.under_fixed f x hx, Key.under_fixed f y hy] at hxy
  · obtain ⟨a, _, rfl⟩ := Context.mem_rekey.mp hy
    rw [Key.under_fixed f x hx, Key.under_lift] at hxy
    have hn := congrArg Key.name hxy
    have he : liftName 0 (f a.name) = .var 0 := hn.symm.trans hx
    exact False.elim (liftName_zero_ne_var_zero _ he)
  · obtain ⟨a, _, rfl⟩ := Context.mem_rekey.mp hx
    rw [Key.under_lift, Key.under_fixed f y hy] at hxy
    have hn := congrArg Key.name hxy
    have he : liftName 0 (f a.name) = .var 0 := hn.trans hy
    exact False.elim (liftName_zero_ne_var_zero _ he)
  · exact injOn_under_lift hf hx hy hxy

/-- **Injectivity of rekeying survives updating an owned key.**
Updating an already-owned key introduces no new aliasing obligation. -/
theorem Context.injOn_insert_owned {f : Key → Key} {Δ : Context}
    {e : Key} {c : Capability} (hf : Set.InjOn f {d | d ∈ Δ}) (he : e ∈ Δ) :
    Set.InjOn f {d | d ∈ Δ.insert e c} := by
  intro x hx y hy hxy
  have hx' : x ∈ Δ := (Finmap.mem_insert.mp hx).elim (fun h => h ▸ he) id
  have hy' : y ∈ Δ := (Finmap.mem_insert.mp hy).elim (fun h => h ▸ he) id
  exact hf hx' hy' hxy

/-- **Injectivity of rekeying under a restriction binding.**
Both newly restricted roles lie in the collision-free binder domain. -/
theorem Context.injOn_under_bind {f : Name → Name} {Δ : Context}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) (c : Capability) :
    Set.InjOn (Key.mapName (under f)) {e | e ∈ Context.bind c Δ} := by
  have hd : ∀ e ∈ Context.bind c Δ,
      e.name = .var 0 ∨ e ∈ Context.lift 0 Δ := by
    intro e he
    rcases Finmap.mem_insert.mp he with he | he
    · exact Or.inl (congrArg Key.name he)
    · rcases Finmap.mem_insert.mp he with he | he
      · exact Or.inl (congrArg Key.name he)
      · exact Or.inr he
  intro x hx y hy hxy
  exact injOn_under_binder hf (hd x hx) (hd y hy) hxy

/-- **Linear input installs the received role on the bound name.**
Linear input installs precisely the transmitted role on its bound name. -/
theorem Context.lookup_received (Δ : Context) (r : Role) (c : Capability) :
    ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c).lookup ⟨.var 0, r⟩ = some c := by
  simp

/-- **Rekeying commutes with binding a private pair.**
Restriction rekeying fixes its newly bound pair and transports exactly
the outer context; it cannot alias either fresh role with an outer key. -/
theorem Context.rekey_bind {f : Name → Name} {Δ : Context} {c : Capability}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ})
    (hu : Set.InjOn (Key.mapName (under f)) {e | e ∈ Context.bind c Δ}) :
    rekey (Key.mapName (under f)) (Context.bind c Δ) hu =
      Context.bind c (rekey (Key.mapName f) Δ hf) := by
  apply Finmap.ext
  simp only [rekey, Context.entries_bind, Multiset.map_cons]
  exact congrArg (fun m : Multiset (Sigma (fun _ : Key => Capability)) =>
    ⟨⟨.var 0, .negative⟩, c.dual⟩ ::ₘ ⟨⟨.var 0, .positive⟩, c⟩ ::ₘ m)
    (congrArg Finmap.entries (rekey_under_lift hf (injOn_under_lift hf)))

/-- **Received role's opposite is absent at the bound name.**
A received role cannot duplicate an existing key of the opposite role. -/
theorem Context.lookup_received_opposite (Δ : Context) (r : Role) (c : Capability) :
    ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c).lookup ⟨.var 0, r.opposite⟩ = none := by
  rw [Finmap.lookup_insert_of_ne _ (by
    intro h
    have hr := congrArg Key.role h
    exact Key.opposite_ne ⟨.var 0, r⟩ (Key.ext rfl hr))]
  exact Finmap.lookup_eq_none.mpr (Context.fresh_lift Δ r.opposite)

/-- **Injectivity of rekeying after receiving a fresh role.**
A linear input's fresh variable role preserves collision freedom of
all lifted outer keys, including outer keys of the opposite role. -/
theorem Context.injOn_under_received {f : Name → Name} {Δ : Context}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) (r : Role) (c : Capability) :
    Set.InjOn (Key.mapName (under f))
      {e | e ∈ (Context.lift 0 Δ).insert ⟨.var 0, r⟩ c} := by
  have hd : ∀ e ∈ (Context.lift 0 Δ).insert ⟨.var 0, r⟩ c,
      e.name = .var 0 ∨ e ∈ Context.lift 0 Δ := by
    intro e he
    rcases Finmap.mem_insert.mp he with he | he
    · exact Or.inl (congrArg Key.name he)
    · exact Or.inr he
  intro x hx y hy hxy
  exact injOn_under_binder hf (hd x hx) (hd y hy) hxy

/-- **Injectivity of rekeying survives erasing a key.**
Erasing an owned key cannot create a rekeying collision. -/
theorem Context.injOn_erase {f : Key → Key} {Δ : Context} {e : Key}
    (hf : Set.InjOn f {d | d ∈ Δ}) : Set.InjOn f {d | d ∈ Δ.erase e} := by
  intro x hx y hy hxy
  exact hf (Finmap.mem_erase.mp hx).2 (Finmap.mem_erase.mp hy).2 hxy

end Cslib.SessionTypes.Endpoint
