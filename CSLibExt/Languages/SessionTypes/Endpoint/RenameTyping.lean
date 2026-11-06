/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.TypingTransport

/-!
# Syntax-directed typing transport under collision-free name maps

The final transport theorem uses structural induction on typing. The private
constructor lemmas receive only their induction hypotheses, not a stored
preservation oracle.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

set_option backward.isDefEq.respectTransparency false in
private theorem rename_outName {n m : Nat} {Δ : Context} {e : Key}
    {c : Capability} {b : Name} {s : Protocol} {p : Proc} {f : Name → Name}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendName s)
    (ha : e.name.ClosedAt n) (hb : b.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {d | d ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {d | d ∈ Δ.insert e ⟨c.rank, s⟩})
    (hp : HasType m (Context.rekey (Key.mapName f) (Δ.insert e ⟨c.rank, s⟩) hi)
      (mapProc f p)) :
    HasType m (Context.rekey (Key.mapName f) Δ hf)
      (mapProc f (.out e.name b p)) := by
  have hU : Set.InjOn (Key.mapName f) {d | d = e ∨ d ∈ Δ} := by
    intro x hx y hy hxy
    exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
  apply HasType.outName (e := Key.mapName f e) (c := c) (s := s)
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope e.name ha
  · exact hscope b hb
  · rw [← Context.rekey_insert hf hi hU]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem rename_inpName {n m : Nat} {Δ : Context} {e : Key}
    {c : Capability} {s : Protocol} {p : Proc} {f : Name → Name}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvName s)
    (ha : e.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {d | d ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {d | d ∈ Δ.insert e ⟨c.rank, s⟩})
    (hu : Set.InjOn (Key.mapName (under f))
      {d | d ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)})
    (hp : HasType (m + 1)
      (Context.rekey (Key.mapName (under f))
        (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) hu) (mapProc (under f) p)) :
    HasType m (Context.rekey (Key.mapName f) Δ hf)
      (mapProc f (.inp e.name p)) := by
  have hU : Set.InjOn (Key.mapName f) {d | d = e ∨ d ∈ Δ} := by
    intro x hx y hy hxy
    exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
  apply HasType.inpName (e := Key.mapName f e) (c := c) (s := s)
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope e.name ha
  · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem rename_outEndpoint {n m k : Nat} {Δ : Context} {e d : Key}
    {c : Capability} {t s : Protocol} {p : Proc} {f : Name → Name}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendEndpoint d.role k t s)
    (hd : Δ.lookup d = some ⟨k, t⟩) (hne : e ≠ d)
    (ha : e.name.ClosedAt n) (hb : d.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {a | a ∈ Δ})
    (hE : Set.InjOn (Key.mapName f) {a | a ∈ Δ.erase d})
    (hi : Set.InjOn (Key.mapName f) {a | a ∈ (Δ.erase d).insert e ⟨c.rank, s⟩})
    (hp : HasType m
      (Context.rekey (Key.mapName f) ((Δ.erase d).insert e ⟨c.rank, s⟩) hi)
      (mapProc f p)) :
    HasType m (Context.rekey (Key.mapName f) Δ hf)
      (mapProc f (.out e.name d.name p)) := by
  have hm := Finmap.mem_of_lookup_eq_some hd
  have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ.erase d} := by
    intro x hx y hy hxy
    exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
  apply HasType.outEndpoint (e := Key.mapName f e) (d := Key.mapName f d)
    (c := c) (k := k) (t := t) (s := s)
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact Context.lookup_rekey.mpr ⟨d, hd, rfl⟩
  · intro he
    exact hne (hf (Finmap.mem_of_lookup_eq_some hc) hm he)
  · exact hscope e.name ha
  · exact hscope d.name hb
  · rw [← Context.rekey_erase hm hf hE, ← Context.rekey_insert hE hi hU]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem rename_inpEndpoint {n m k : Nat} {Δ : Context} {e : Key}
    {c : Capability} {r : Role} {t s : Protocol} {p : Proc} {f : Name → Name}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvEndpoint r k t s)
    (ha : e.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {a | a ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {a | a ∈ Δ.insert e ⟨c.rank, s⟩})
    (hu : Set.InjOn (Key.mapName (under f))
      {a | a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)})
    (hR : Set.InjOn (Key.mapName (under f))
      {a | a ∈ (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩})
    (hp : HasType (m + 1) (Context.rekey (Key.mapName (under f))
      ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) hR)
      (mapProc (under f) p)) :
    HasType m (Context.rekey (Key.mapName f) Δ hf)
      (mapProc f (.inp e.name p)) := by
  have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} := by
    intro x hx y hy hxy
    exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
  have hUR : Set.InjOn (Key.mapName (under f))
      {a | a = ⟨.var 0, r⟩ ∨ a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)} := by
    intro x hx y hy hxy
    exact hR (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
  apply HasType.inpEndpoint (e := Key.mapName f e) (c := c) (r := r)
    (k := k) (t := t) (s := s)
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope e.name ha
  · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
    have heq := Context.rekey_insert hu hR hUR
    have hfix : Key.mapName (under f) (⟨.var 0, r⟩ : Key) = ⟨.var 0, r⟩ := rfl
    rw [hfix] at heq
    rw [← heq]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem rename_par {m : Nat} {Δ Θ : Context} {p q : Proc} {f : Name → Name}
    (hd : Finmap.Disjoint Δ Θ)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ})
    (hg : Set.InjOn (Key.mapName f) {e | e ∈ Θ})
    (hu : Set.InjOn (Key.mapName f) {e | e ∈ Δ ∪ Θ})
    (hp : HasType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f p))
    (hq : HasType m (Context.rekey (Key.mapName f) Θ hg) (mapProc f q)) :
    HasType m (Context.rekey (Key.mapName f) (Δ ∪ Θ) hu) (mapProc f (.par p q)) := by
  rw [Context.rekey_union hf hg hu hd]
  apply HasType.par ?_ hp hq
  apply Context.disjoint_rekey hf hg
  · intro x hx y hy hxy
    exact hu (Finmap.mem_union.mpr hx) (Finmap.mem_union.mpr hy) hxy
  · exact hd

private theorem rename_nu {m : Nat} {Δ : Context} {p : Proc}
    {f : Name → Name} {c : Capability}
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ})
    (hu : Set.InjOn (Key.mapName (under f)) {e | e ∈ Context.bind c Δ})
    (hp : HasType (m + 1)
      (Context.rekey (Key.mapName (under f)) (Context.bind c Δ) hu)
      (mapProc (under f) p)) :
    HasType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f (.nu p)) := by
  apply HasType.nu (c := c)
  rw [← Context.rekey_bind hf hu]
  exact hp

private theorem rename_nil {n m : Nat} {Δ : Context} {f : Name → Name}
    (hc : Δ.Completed) (hs : ∀ e ∈ Δ, e.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    HasType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f .nil) := by
  apply HasType.nil (hc.rekey hf)
  intro e he
  obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
  exact hscope d.name (hs d hd)

/-- **Collision-free renaming preserves endpoint typing.**
Capture-safe rekeying transports all finite-process endpoint typing,
including linear payloads and actual input/ν binders. Collision freedom is
required only on owned keys and can be derived from a delegation split. -/
theorem HasType.rename {n m : Nat} {Δ : Context} {p : Proc} {f : Name → Name}
    (h : HasType n Δ p) (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    HasType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f p) := by
  induction h generalizing m f with
  | nil hc hs => exact rename_nil hc hs hscope hf
  | @outName n Δ e c b s p hc hs ha hb hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    exact rename_outName hc hs ha hb hscope hf hi (ih hscope hi)
  | @inpName n Δ e c s p hc hs ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    exact rename_inpName hc hs ha hscope hf hi hu
      (ih (fun _ h => under_scoped hscope h) hu)
  | @outEndpoint n Δ e d c k t s p hc hs hd hne ha hb hp ih =>
    have hE := Context.injOn_erase hf (e := d)
    have hm : e ∈ Δ.erase d := Finmap.mem_erase.mpr
      ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hE hm
    exact rename_outEndpoint hc hs hd hne ha hb hscope hf hE hi (ih hscope hi)
  | @inpEndpoint n Δ e c r k t s p hc hs ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hR := Context.injOn_under_received hi r (⟨k, t⟩ : Capability)
    exact rename_inpEndpoint hc hs ha hscope hf hi hu hR
      (ih (fun _ h => under_scoped hscope h) hR)
  | @par n Δ Θ p q hd hp hq ihp ihq =>
    have hΔ : Set.InjOn (Key.mapName f) {e | e ∈ Δ} := by
      intro x hx y hy hxy
      exact hf (Finmap.mem_union.mpr (Or.inl hx))
        (Finmap.mem_union.mpr (Or.inl hy)) hxy
    have hΘ : Set.InjOn (Key.mapName f) {e | e ∈ Θ} := by
      intro x hx y hy hxy
      exact hf (Finmap.mem_union.mpr (Or.inr hx))
        (Finmap.mem_union.mpr (Or.inr hy)) hxy
    exact rename_par hd hΔ hΘ hf (ihp hscope hΔ) (ihq hscope hΘ)
  | @nu n Δ c p hp ih =>
    have hu := Context.injOn_under_bind hf c
    exact rename_nu hf hu (ih (fun _ h => under_scoped hscope h) hu)

/-- **Binder lifting preserves endpoint typing.**
Any ambient binder lift transports full endpoint typing without
changing protocols, roles or resource multiplicity. -/
theorem HasType.lift {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) (k : Nat) :
    HasType (n + 1) (Context.lift k Δ) (liftProc k p) := by
  have hf : Set.InjOn (Key.mapName (liftName k)) {e | e ∈ Δ} := by
    intro x _ y _ hxy
    exact Key.mapName_injective (liftName_injective k) hxy
  have ht := h.rename (fun _ ha => ha.lift) hf
  simpa only [Context.lift, mapProc_liftName] using ht

end Cslib.SessionTypes.Endpoint
