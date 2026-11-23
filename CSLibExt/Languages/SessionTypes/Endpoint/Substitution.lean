/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RenameTyping

/-!
# Linear subject substitution in the existing π syntax

The receive-bound capability is consumed and inserted at the sent endpoint
key. Non-aliasing is an ownership condition derived from parallel splitting;
the opposite role of the same physical name is not an aliasing collision.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- Substitution cancels binder lift on an entire polarized endpoint key. -/
theorem Key.subst_lift (b : Name) (e : Key) :
    mapName (substName b 0) (mapName (liftName 0) e) = e := by
  cases e
  simp [mapName, substName_liftName]

set_option backward.isDefEq.respectTransparency false in
/-- Linear input substitution is collision-free when the transmitted role
was absent from the receiver. Its opposite physical-name role is allowed. -/
theorem Context.injOn_received_subst {Δ : Context} {b : Name} {r : Role}
    {c : Capability} (hfresh : (⟨b, r⟩ : Key) ∉ Δ) :
    Set.InjOn (Key.mapName (substName b 0))
      {e | e ∈ (Context.lift 0 Δ).insert ⟨.var 0, r⟩ c} := by
  intro x hx y hy hxy
  rcases Finmap.mem_insert.mp hx with hx | hx <;>
    rcases Finmap.mem_insert.mp hy with hy | hy
  · exact hx.trans hy.symm
  · subst x
    obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp hy
    change (⟨b, r⟩ : Key) =
      Key.mapName (substName b 0) (Key.mapName (liftName 0) d) at hxy
    rw [Key.subst_lift] at hxy
    exact False.elim (hfresh (hxy.symm ▸ hd))
  · subst y
    obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp hx
    change Key.mapName (substName b 0) (Key.mapName (liftName 0) d) =
      (⟨b, r⟩ : Key) at hxy
    rw [Key.subst_lift] at hxy
    exact False.elim (hfresh (hxy ▸ hd))
  · obtain ⟨a, _, rfl⟩ := Context.mem_rekey.mp hx
    obtain ⟨d, _, rfl⟩ := Context.mem_rekey.mp hy
    rw [Key.subst_lift, Key.subst_lift] at hxy
    rw [hxy]

/-- Subject substitution consumes the bound role and inserts exactly the
sent key, preserving every other capability and permitting its peer role. -/
theorem Context.rekey_received_subst {Δ : Context} {b : Name} {r : Role}
    {c : Capability} (hfresh : (⟨b, r⟩ : Key) ∉ Δ)
    (hi : Set.InjOn (Key.mapName (substName b 0))
      {e | e ∈ (Context.lift 0 Δ).insert ⟨.var 0, r⟩ c}) :
    rekey (Key.mapName (substName b 0))
      ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) hi = Δ.insert ⟨b, r⟩ c := by
  apply Finmap.ext
  change ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c).entries.map
    (fun x => ⟨Key.mapName (substName b 0) x.1, x.2⟩) = (Δ.insert ⟨b, r⟩ c).entries
  rw [Finmap.entries_insert_of_notMem (Context.fresh_lift Δ r),
    Finmap.entries_insert_of_notMem hfresh]
  simp only [Multiset.map_cons]
  congr 1
  change (Δ.entries.map (fun x =>
    (⟨Key.mapName (liftName 0) x.1, x.2⟩ : Sigma (fun _ : Key => Capability)))).map
      (fun x : Sigma (fun _ : Key => Capability) =>
        ⟨Key.mapName (substName b 0) x.1, x.2⟩) = Δ.entries
  rw [Multiset.map_map]
  calc
    _ = Δ.entries.map id := by
      apply Multiset.map_congr rfl
      rintro ⟨e, t⟩ _
      simp [Key.subst_lift]
    _ = _ := Multiset.map_id _

/-- Receiving a linear endpoint substitutes its physical name in ALL
subject and payload positions, removes the bound role and inserts the sent
role exactly once. Capture under input and ν is the canonical π substitution. -/
theorem HasType.subst_endpoint {n : Nat} {Δ : Context} {b : Name}
    {r : Role} {c : Capability} {p : Proc}
    (h : HasType (n + 1) ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) p)
    (hb : b.ClosedAt n) (hfresh : (⟨b, r⟩ : Key) ∉ Δ) :
    HasType n (Δ.insert ⟨b, r⟩ c) (PiCalculus.subst p b) := by
  have hi := Context.injOn_received_subst (c := c) hfresh
  have ht := h.rename (fun _ ha => hb.subst ha (Nat.zero_le n)) hi
  rw [Context.rekey_received_subst hfresh hi, mapProc_substName] at ht
  exact ht

/-- Linear subject substitution with non-aliasing DERIVED from disjoint
sender/receiver ownership and the receiver's already-owned carrier. -/
theorem HasType.subst_endpoint_from_split {n : Nat} {Δ Θ : Context}
    {b : Name} {r : Role} {c old next : Capability} {e : Key} {p : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hs : Δ.lookup ⟨b, r⟩ = some c)
    (hr : Θ.lookup e = some old)
    (hp : HasType (n + 1)
      ((Context.lift 0 (Θ.insert e next)).insert ⟨.var 0, r⟩ c) p)
    (hb : b.ClosedAt n) :
    HasType n ((Θ.insert e next).insert ⟨b, r⟩ c) (PiCalculus.subst p b) := by
  apply hp.subst_endpoint hb
  exact Context.fresh_insert_owned (Context.fresh_of_disjoint hd hs)
    (Finmap.mem_of_lookup_eq_some hr)

/-- Passive input substitution changes no linear context: every owned
key is a lifted outer key, so the input binder owns no endpoint role. -/
theorem Context.rekey_passive_subst {Δ : Context} (b : Name)
    (hi : Set.InjOn (Key.mapName (substName b 0)) {e | e ∈ Context.lift 0 Δ}) :
    rekey (Key.mapName (substName b 0)) (Context.lift 0 Δ) hi = Δ := by
  apply Finmap.ext
  change (Δ.entries.map (fun x =>
    (⟨Key.mapName (liftName 0) x.1, x.2⟩ : Sigma (fun _ : Key => Capability)))).map
      (fun x : Sigma (fun _ : Key => Capability) =>
        ⟨Key.mapName (substName b 0) x.1, x.2⟩) = Δ.entries
  rw [Multiset.map_map]
  calc
    _ = Δ.entries.map id := by
      apply Multiset.map_congr rfl
      rintro ⟨e, c⟩ _
      simp [Key.subst_lift]
    _ = _ := Multiset.map_id _

set_option backward.isDefEq.respectTransparency false in
/-- Passive substitution is collision-free on all lifted outer endpoint keys. -/
theorem Context.injOn_passive_subst {Δ : Context} (b : Name) :
    Set.InjOn (Key.mapName (substName b 0)) {e | e ∈ Context.lift 0 Δ} := by
  intro x hx y hy hxy
  obtain ⟨a, _, rfl⟩ := Context.mem_rekey.mp hx
  obtain ⟨d, _, rfl⟩ := Context.mem_rekey.mp hy
  rw [Key.subst_lift, Key.subst_lift] at hxy
  rw [hxy]

/-- Passive payload substitution preserves every linear obligation and
cannot introduce an endpoint subject capability. -/
theorem HasType.subst_passive {n : Nat} {Δ : Context} {p : Proc} {b : Name}
    (h : HasType (n + 1) (Context.lift 0 Δ) p) (hb : b.ClosedAt n) :
    HasType n Δ (PiCalculus.subst p b) := by
  have hi := Context.injOn_passive_subst (Δ := Δ) b
  have ht := h.rename (fun _ ha => hb.subst ha (Nat.zero_le n)) hi
  rw [Context.rekey_passive_subst b hi, mapProc_substName] at ht
  exact ht

end Cslib.SessionTypes.Endpoint
