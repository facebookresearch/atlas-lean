/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextTransport

/-!
# Finite ownership algebra for typing transport
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

private theorem lookup_insert_if (Δ : Context) (e : Key) (c : Capability)
    (d : Key) : (Δ.insert e c).lookup d =
      if d = e then some c else Δ.lookup d := by
  by_cases h : d = e
  · subst d
    simp
  · simp [Finmap.lookup_insert_of_ne, h]

set_option backward.isDefEq.respectTransparency false in
/-- **Collision-free rekeying commutes with insertion.**
Rekeying commutes with capability insertion when the combined domain
has no key collision. The condition is on ownership, not execution. -/
theorem Context.rekey_insert {f : Key → Key} {Δ : Context} {e : Key}
    {c : Capability} (hΔ : Set.InjOn f {x | x ∈ Δ})
    (hI : Set.InjOn f {x | x ∈ Δ.insert e c})
    (hf : Set.InjOn f {x | x = e ∨ x ∈ Δ}) :
    rekey f (Δ.insert e c) hI = (rekey f Δ hΔ).insert (f e) c := by
  apply Finmap.ext_lookup
  intro x
  apply Option.ext
  intro t
  rw [lookup_rekey]
  by_cases hx : x = f e
  · subst x
    rw [Finmap.lookup_insert]
    constructor
    · rintro ⟨d, hd, hde⟩
      have hm := Finmap.mem_of_lookup_eq_some hd
      have he : d = e := hf (Finmap.mem_insert.mp hm) (Or.inl rfl) hde
      subst d
      simpa only [Finmap.lookup_insert] using hd
    · intro ht
      exact ⟨e, by simpa only [Finmap.lookup_insert] using ht, rfl⟩
  · rw [Finmap.lookup_insert_of_ne _ hx, lookup_rekey]
    constructor
    · rintro ⟨d, hd, hdx⟩
      have he : d ≠ e := by
        intro h
        exact hx (h ▸ hdx.symm)
      rw [lookup_insert_if, ite_eq_right he] at hd
      exact ⟨d, hd, hdx⟩
    · rintro ⟨d, hd, hdx⟩
      have he : d ≠ e := by
        intro h
        exact hx (h ▸ hdx.symm)
      refine ⟨d, ?_, hdx⟩
      rw [lookup_insert_if, ite_eq_right he]
      exact hd

set_option backward.isDefEq.respectTransparency false in
/-- **Collision-free rekeying commutes with erasing an owned key.**
Erasing an owned key commutes with collision-free rekeying. -/
theorem Context.rekey_erase {f : Key → Key} {Δ : Context} {e : Key}
    (he : e ∈ Δ) (hΔ : Set.InjOn f {x | x ∈ Δ})
    (hE : Set.InjOn f {x | x ∈ Δ.erase e}) :
    rekey f (Δ.erase e) hE = (rekey f Δ hΔ).erase (f e) := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = f e
  · subst x
    rw [Finmap.lookup_erase]
    apply Finmap.lookup_eq_none.mpr
    intro h
    obtain ⟨d, hd, hde⟩ := mem_rekey.mp h
    obtain ⟨hne, hm⟩ := Finmap.mem_erase.mp hd
    exact hne (hΔ hm he hde)
  · apply Option.ext
    intro c
    rw [lookup_rekey, Finmap.lookup_erase_ne hx, lookup_rekey]
    constructor
    · rintro ⟨d, hd, hdx⟩
      have hne : d ≠ e := by
        intro h
        exact hx (h ▸ hdx.symm)
      rw [Finmap.lookup_erase_ne hne] at hd
      exact ⟨d, hd, hdx⟩
    · rintro ⟨d, hd, hdx⟩
      have hne : d ≠ e := by
        intro h
        exact hx (h ▸ hdx.symm)
      exact ⟨d, by simpa only [Finmap.lookup_erase_ne hne] using hd, hdx⟩

private theorem lookup_disjoint_union {Δ Θ : Context}
    (hd : Finmap.Disjoint Δ Θ) (e : Key) (c : Capability) :
    (Δ ∪ Θ).lookup e = some c ↔
      Δ.lookup e = some c ∨ Θ.lookup e = some c := by
  rw [Finmap.mem_lookup_union']
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨?_, h⟩
      intro he
      exact hd e he (Finmap.mem_of_lookup_eq_some h)

set_option backward.isDefEq.respectTransparency false in
/-- **Collision-free rekeying commutes with a disjoint union.**
Collision-free rekeying commutes with a linear parallel split. -/
theorem Context.rekey_union {f : Key → Key} {Δ Θ : Context}
    (hΔ : Set.InjOn f {e | e ∈ Δ}) (hΘ : Set.InjOn f {e | e ∈ Θ})
    (hUnion : Set.InjOn f {e | e ∈ Δ ∪ Θ}) (hd : Finmap.Disjoint Δ Θ) :
    rekey f (Δ ∪ Θ) hUnion = rekey f Δ hΔ ∪ rekey f Θ hΘ := by
  have hf : Set.InjOn f {e | e ∈ Δ ∨ e ∈ Θ} := by
    intro x hx y hy hxy
    exact hUnion (Finmap.mem_union.mpr hx) (Finmap.mem_union.mpr hy) hxy
  have hd' := disjoint_rekey hΔ hΘ hf hd
  apply Finmap.ext_lookup
  intro e
  apply Option.ext
  intro c
  rw [lookup_rekey, lookup_disjoint_union hd', lookup_rekey, lookup_rekey]
  simp only [lookup_disjoint_union hd, or_and_right, exists_or]

set_option backward.isDefEq.respectTransparency false in
/-- **Context lifting commutes with insertion.**
Context lifting commutes with endpoint advancement at any cutoff. -/
theorem Context.lift_insert (k : Nat) (Δ : Context) (e : Key) (c : Capability) :
    lift k (Δ.insert e c) = (lift k Δ).insert (Key.mapName (PiCalculus.liftName k) e) c := by
  apply rekey_insert
  intro x _ y _ hxy
  exact Key.mapName_injective (liftName_injective k) hxy

/-- **Owned keys are absent from the other side of a disjoint split.**
A sent endpoint is absent from the other side of a linear split. -/
theorem Context.fresh_of_disjoint {Δ Θ : Context} {e : Key} {c : Capability}
    (hd : Finmap.Disjoint Δ Θ) (he : Δ.lookup e = some c) : e ∉ Θ :=
  hd e (Finmap.mem_of_lookup_eq_some he)

/-- **Updating an owned key keeps absent keys absent.**
Advancing another already-owned carrier does not create a payload alias. -/
theorem Context.fresh_insert_owned {Δ : Context} {e d : Key} {c : Capability}
    (hd : d ∉ Δ) (he : e ∈ Δ) : d ∉ Δ.insert e c := by
  intro hm
  rcases Finmap.mem_insert.mp hm with hm | hm
  · exact hd (hm ▸ he)
  · exact hd hm

/-- **Updating an owned key preserves a disjoint split.**
Advancing an already-owned endpoint preserves a disjoint split. -/
theorem Context.disjoint_insert_owned {Δ Θ : Context} {e : Key} {c : Capability}
    (hd : Finmap.Disjoint Δ Θ) (he : e ∈ Δ) :
    Finmap.Disjoint (Δ.insert e c) Θ := by
  intro d hm ht
  rcases Finmap.mem_insert.mp hm with hm | hm
  · subst d
    exact hd e he ht
  · exact hd d hm ht

/-- **Updating owned keys on both sides of a disjoint union.**
Advancing both peers across a disjoint split advances exactly those
two keys in the combined interface, with no other capability change. -/
theorem Context.union_insert_owned {Δ Θ : Context} {e d : Key} {c t : Capability}
    (hd : Finmap.Disjoint Δ Θ) (he : e ∈ Δ) (ht : d ∈ Θ) :
    Δ.insert e c ∪ Θ.insert d t = ((Δ ∪ Θ).insert e c).insert d t := by
  have hleft := disjoint_insert_owned (c := c) hd he
  have hright := disjoint_insert_owned (c := t) (Finmap.Disjoint.symm _ _ hleft) ht
  rw [Finmap.union_comm_of_disjoint (Finmap.Disjoint.symm _ _ hright)]
  rw [← Finmap.insert_union]
  rw [Finmap.union_comm_of_disjoint (Finmap.Disjoint.symm _ _ hleft)]
  rw [← Finmap.insert_union]

/-- **Capability transfer with carrier updates preserves disjointness.**
Capability transfer is a disjoint ownership move, including when the
sender and receiver also advance their distinct carrier roles. -/
theorem Context.disjoint_transfer {Δ Θ : Context} {e f d : Key}
    {c t u : Capability} (hd : Finmap.Disjoint Δ Θ)
    (he : e ∈ Δ) (hf : f ∈ Θ) (hne : e ≠ d) :
    Finmap.Disjoint ((Δ.erase d).insert e c) ((Θ.insert f t).insert d u) := by
  intro x hx hy
  have hxo : x ∈ Δ := by
    rcases Finmap.mem_insert.mp hx with hx | hx
    · exact hx ▸ he
    · exact (Finmap.mem_erase.mp hx).2
  have hxd : x ≠ d := by
    rcases Finmap.mem_insert.mp hx with hx | hx
    · exact hx ▸ hne
    · exact (Finmap.mem_erase.mp hx).1
  rcases Finmap.mem_insert.mp hy with hy | hy
  · exact hxd hy
  · rcases Finmap.mem_insert.mp hy with hy | hy
    · exact hd x hxo (hy ▸ hf)
    · exact hd x hxo hy

/-- **Moving a capability across a union preserves the union.**
Moving a capability out of one map into the other preserves the exact
combined interface, including completed endpoint slots. -/
theorem Context.transfer_union {Δ Θ : Context} {d : Key} {c : Capability}
    (hc : Δ.lookup d = some c) : Δ.erase d ∪ Θ.insert d c = Δ ∪ Θ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hxd : x = d
  · subst x
    rw [Finmap.lookup_union_right Finmap.notMem_erase_self, Finmap.lookup_insert,
      Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc), hc]
  · by_cases hx : x ∈ Δ
    · have he : x ∈ Δ.erase d := Finmap.mem_erase.mpr ⟨hxd, hx⟩
      rw [Finmap.lookup_union_left he, Finmap.lookup_erase_ne hxd,
        Finmap.lookup_union_left hx]
    · have he : x ∉ Δ.erase d := fun h => hx (Finmap.mem_erase.mp h).2
      rw [Finmap.lookup_union_right he, Finmap.lookup_insert_of_ne _ hxd,
        Finmap.lookup_union_right hx]

/-- **Erase-and-insert transfer preserves disjointness.**
Removing a key from the sender and inserting it at the receiver
preserves disjoint endpoint ownership. -/
theorem Context.disjoint_erased_transfer {Δ Θ : Context} {d : Key} {c : Capability}
    (hd : Finmap.Disjoint Δ Θ) : Finmap.Disjoint (Δ.erase d) (Θ.insert d c) := by
  intro e he ht
  obtain ⟨hne, hm⟩ := Finmap.mem_erase.mp he
  rcases Finmap.mem_insert.mp ht with ht | ht
  · exact hne ht
  · exact hd e hm ht

/-- **Combined context after delegation and two carrier updates.**
Delegation plus two carrier advances preserves every other key in the
combined context; the sent capability is moved, not duplicated or dropped. -/
theorem Context.transfer_union_insert_owned {Δ Θ : Context} {e f d : Key}
    {c t u : Capability} (hd : Finmap.Disjoint Δ Θ)
    (he : e ∈ Δ) (hf : f ∈ Θ) (hu : Δ.lookup d = some u) (hne : e ≠ d) :
    (Δ.erase d).insert e c ∪ (Θ.insert f t).insert d u =
      ((Δ ∪ Θ).insert e c).insert f t := by
  have hfd : f ≠ d := by
    intro h
    exact hd d (Finmap.mem_of_lookup_eq_some hu) (h ▸ hf)
  rw [Finmap.insert_insert_of_ne (s := Θ) (a := f) (a' := d) hfd]
  have hbase := disjoint_erased_transfer (c := u) (d := d) hd
  have he' : e ∈ Δ.erase d := Finmap.mem_erase.mpr ⟨hne, he⟩
  have hf' : f ∈ Θ.insert d u := Finmap.mem_insert.mpr (Or.inr hf)
  rw [union_insert_owned hbase he' hf', transfer_union hu]

/-- **Erasing a different key commutes with insertion.**
Erasing a different endpoint commutes with insertion, which is needed
when an unused completed slot passes through a delegation prefix. -/
theorem Context.erase_insert_ne {Δ : Context} {e d : Key} {c : Capability}
    (hne : e ≠ d) : (Δ.insert e c).erase d = (Δ.erase d).insert e c := by
  apply Finmap.ext_lookup
  intro x
  by_cases hxd : x = d
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_insert_of_ne _ hne.symm,
      Finmap.lookup_erase]
  · by_cases hxe : x = e
    · subst x
      rw [Finmap.lookup_erase_ne hne, Finmap.lookup_insert, Finmap.lookup_insert]
    · rw [Finmap.lookup_erase_ne hxd, Finmap.lookup_insert_of_ne _ hxe,
        Finmap.lookup_insert_of_ne _ hxe, Finmap.lookup_erase_ne hxd]

/-- **Inserting a key absent from the other side preserves disjointness.**
An insertion disjoint from the other side preserves a linear split,
including the unused completed slots transported by structural congruence. -/
theorem Context.disjoint_insert_fresh {Δ Θ : Context} {e : Key} {c : Capability}
    (hd : Finmap.Disjoint Δ Θ) (he : e ∉ Θ) :
    Finmap.Disjoint (Δ.insert e c) Θ := by
  intro d hm ht
  rcases Finmap.mem_insert.mp hm with hm | hm
  · subst d
    exact he ht
  · exact hd d hm ht

/-- **Restriction binding commutes with inserting an outer key.**
Inserting an outer endpoint before restriction is the same as
inserting its lifted key after the fresh dual pair has been bound. -/
theorem Context.bind_insert (c u : Capability) (Δ : Context) (e : Key) :
    Context.bind c (Δ.insert e u) =
      (Context.bind c Δ).insert (Key.mapName (PiCalculus.liftName 0) e) u := by
  rw [Context.bind, Context.bind, Context.lift_insert]
  rw [Finmap.insert_insert_of_ne (s := Context.lift 0 Δ)
    (a := Key.mapName (PiCalculus.liftName 0) e) (a' := (⟨.var 0, .positive⟩ : Key))
    (Key.lift_ne_bound e .positive)]
  rw [Finmap.insert_insert_of_ne
    (s := (Context.lift 0 Δ).insert (⟨.var 0, .positive⟩ : Key) c)
    (a := Key.mapName (PiCalculus.liftName 0) e) (a' := (⟨.var 0, .negative⟩ : Key))
    (Key.lift_ne_bound e .negative)]

/-- **Inserting a left-absent key into a union updates the right part.**
Inserting a key absent from the left component updates only the right
component of a left-biased finite-map union. -/
theorem Context.insert_union_right_of_fresh {Δ Θ : Context} {e : Key}
    {c : Capability} (he : e ∉ Δ) :
    (Δ ∪ Θ).insert e c = Δ ∪ Θ.insert e c := by
  apply Finmap.ext_lookup
  intro x
  by_cases hxe : x = e
  · subst x
    rw [Finmap.lookup_insert, Finmap.lookup_union_right he, Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ hxe]
    by_cases hx : x ∈ Δ
    · rw [Finmap.lookup_union_left hx, Finmap.lookup_union_left hx]
    · rw [Finmap.lookup_union_right hx, Finmap.lookup_union_right hx,
        Finmap.lookup_insert_of_ne _ hxe]

set_option backward.isDefEq.respectTransparency false in
/-- **Context lifting commutes with erasing an owned key.**
Erasing an owned outer key commutes with canonical context lifting. -/
theorem Context.lift_erase {Δ : Context} {e : Key} (k : Nat) (he : e ∈ Δ) :
    Context.lift k (Δ.erase e) =
      (Context.lift k Δ).erase (Key.mapName (PiCalculus.liftName k) e) := by
  exact Context.rekey_erase he _ _

/-- **Restriction binding commutes with erasing an owned outer key.**
Erasing an owned outer role commutes with restriction's fresh dual pair. -/
theorem Context.bind_erase {Δ : Context} {e : Key} (c : Capability) (he : e ∈ Δ) :
    (Context.bind c Δ).erase (Key.mapName (PiCalculus.liftName 0) e) =
      Context.bind c (Δ.erase e) := by
  rw [Context.bind, Context.bind]
  rw [Context.erase_insert_ne (Key.lift_ne_bound e .negative).symm,
    Context.erase_insert_ne (Key.lift_ne_bound e .positive).symm,
    ← Context.lift_erase 0 he]

/-- **Erasure distributes over union.**
Erasure distributes through the exact finite ownership union. -/
theorem Context.erase_union (Δ Θ : Context) (e : Key) :
    (Δ ∪ Θ).erase e = Δ.erase e ∪ Θ.erase e := by
  apply Finmap.ext_lookup
  intro x
  by_cases hxe : x = e
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_union_right Finmap.notMem_erase_self,
      Finmap.lookup_erase]
  · by_cases hx : x ∈ Δ
    · have hxE := Finmap.mem_erase.mpr ⟨hxe, hx⟩
      rw [Finmap.lookup_erase_ne hxe, Finmap.lookup_union_left hx,
        Finmap.lookup_union_left hxE, Finmap.lookup_erase_ne hxe]
    · have hxE : x ∉ Δ.erase e := fun hm => hx (Finmap.mem_erase.mp hm).2
      rw [Finmap.lookup_erase_ne hxe, Finmap.lookup_union_right hx,
        Finmap.lookup_union_right hxE, Finmap.lookup_erase_ne hxe]

/-- **Erasing an absent key changes nothing.** Erasing an absent key changes no ownership entry. -/
theorem Context.erase_of_notMem {Δ : Context} {e : Key} (he : e ∉ Δ) :
    Δ.erase e = Δ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = e
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_eq_none.mpr he]
  · exact Finmap.lookup_erase_ne hx

set_option backward.isDefEq.respectTransparency false in
/-- **Context lifting preserves a disjoint union.**
Canonical lifting preserves a disjoint ownership union exactly. -/
theorem Context.lift_union (k : Nat) {Δ Θ : Context} (hd : Finmap.Disjoint Δ Θ) :
    Context.lift k (Δ ∪ Θ) = Context.lift k Δ ∪ Context.lift k Θ := by
  exact Context.rekey_union _ _ _ hd

/-- **Binding a fresh pair keeps disjointness from a lifted context.**
A fresh bound pair belongs only to the left component of a lifted split. -/
theorem Context.disjoint_bind_lift {Δ Θ : Context} (c : Capability)
    (hd : Finmap.Disjoint Δ Θ) :
    Finmap.Disjoint (Context.bind c Δ) (Context.lift 0 Θ) := by
  have hl : Finmap.Disjoint (Context.lift 0 Δ) (Context.lift 0 Θ) :=
    Context.disjoint_rekey _ _
      (fun _ _ _ _ h => Key.mapName_injective (liftName_injective 0) h) hd
  intro e he ht
  rw [Context.bind] at he
  rcases Finmap.mem_insert.mp he with he | he
  · exact Context.fresh_lift Θ .negative (he ▸ ht)
  · rcases Finmap.mem_insert.mp he with he | he
    · exact Context.fresh_lift Θ .positive (he ▸ ht)
    · exact hl e he ht

/-- **Restriction binding of a disjoint union.**
Scope extrusion keeps the dual pair on the restricted component and
lifts exactly the unrelated outer partner ownership. -/
theorem Context.bind_union {Δ Θ : Context} (c : Capability)
    (hd : Finmap.Disjoint Δ Θ) :
    Context.bind c (Δ ∪ Θ) = Context.bind c Δ ∪ Context.lift 0 Θ := by
  rw [Context.bind, Context.bind, Context.lift_union 0 hd,
    Finmap.insert_union, Finmap.insert_union]

/-- **Reinserting an owned capability changes nothing.**
Reinstalling exactly an already-owned capability changes no entry. -/
theorem Context.insert_of_lookup {Γ : Context} {e : Key} {c : Capability}
    (hc : Γ.lookup e = some c) : Γ.insert e c = Γ := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = e
  · subst x
    rw [Finmap.lookup_insert, hc]
  · exact Finmap.lookup_insert_of_ne Γ hx

/-- **Insertion after erasing the same key.**
Reinstalling a key overrides any previous entry, so prior erasure of
that same key is immaterial. -/
theorem Context.insert_erase_same (Γ : Context) (e : Key) (c : Capability) :
    (Γ.erase e).insert e c = Γ.insert e c := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = e
  · subst x
    rw [Finmap.lookup_insert, Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ hx, Finmap.lookup_erase_ne hx,
      Finmap.lookup_insert_of_ne _ hx]

/-- **Erasure after inserting the same key.**
Erasing an inserted key removes its entry, independently of its value. -/
theorem Context.erase_insert_same (Γ : Context) (e : Key) (c : Capability) :
    (Γ.insert e c).erase e = Γ.erase e := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = e
  · subst x
    rw [Finmap.lookup_erase, Finmap.lookup_erase]
  · rw [Finmap.lookup_erase_ne hx, Finmap.lookup_insert_of_ne _ hx,
      Finmap.lookup_erase_ne hx]

/-- **Reinstalling the bound pair after erasing its slots.**
Reinstalling the bound pair after removing its old slots restores the
same exact map as installing that pair directly. -/
theorem Context.restore_erased_pair (Γ : Context) (c : Capability) :
    (((Γ.erase (⟨.var 0, .negative⟩ : Key)).erase (⟨.var 0, .positive⟩ : Key)).insert
      (⟨.var 0, .positive⟩ : Key) c).insert (⟨.var 0, .negative⟩ : Key) c.dual =
    (Γ.insert (⟨.var 0, .positive⟩ : Key) c).insert
      (⟨.var 0, .negative⟩ : Key) c.dual := by
  rw [Context.insert_erase_same]
  rw [Finmap.insert_insert_of_ne (s := Γ.erase (⟨.var 0, .negative⟩ : Key))
    (a := (⟨.var 0, .positive⟩ : Key)) (a' := (⟨.var 0, .negative⟩ : Key)) (by decide)]
  rw [Context.insert_erase_same]
  rw [Finmap.insert_insert_of_ne (s := Γ)
    (a := (⟨.var 0, .negative⟩ : Key)) (a' := (⟨.var 0, .positive⟩ : Key)) (by decide)]

/-- **Erasing the bound pair leaves the lifted context.**
Removing the two freshly bound roles exposes exactly the lifted
external context, including every unrelated completed resource. -/
theorem Context.erase_bind_pair (c : Capability) (Δ : Context) :
    ((Context.bind c Δ).erase (⟨.var 0, .negative⟩ : Key)).erase
      (⟨.var 0, .positive⟩ : Key) = Context.lift 0 Δ := by
  rw [Context.bind, Context.erase_insert_same]
  rw [Context.erase_insert_ne (by decide :
    (⟨.var 0, .positive⟩ : Key) ≠ (⟨.var 0, .negative⟩ : Key))]
  rw [Context.erase_of_notMem (Context.fresh_lift Δ .negative),
    Context.erase_insert_same, Context.erase_of_notMem (Context.fresh_lift Δ .positive)]

end Cslib.SessionTypes.Endpoint
