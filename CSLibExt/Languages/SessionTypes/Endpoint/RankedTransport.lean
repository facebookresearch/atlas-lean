/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.TypingTransport

/-!
# Capture-safe name transport of the priority refinement

The ownership equations are shared with plain typing transport. Ranks and
protocols are unchanged by name mapping, and GuardMin transports on the same
owned-key injectivity condition, including newly received and restricted roles.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

set_option backward.isDefEq.respectTransparency false in
private theorem ranked_out_name {n m : Nat} {Δ : Context} {e : Key}
    {c : Capability} {s : Protocol} {b : Name} {p : Proc} {f : Name → Name}
    (hg : GuardMin Δ e c.rank) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendName s) (ha : e.name.ClosedAt n) (hb : b.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {d | d ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {d | d ∈ Δ.insert e ⟨c.rank, s⟩})
    (hp : RankedType m (Context.rekey (Key.mapName f) (Δ.insert e ⟨c.rank, s⟩) hi)
      (mapProc f p)) :
    RankedType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f (.out e.name b p)) := by
  apply RankedType.outName (e := Key.mapName f e) (c := c) (s := s)
  · exact hg.rekey hf
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope _ ha
  · exact hscope _ hb
  · have hU : Set.InjOn (Key.mapName f) {d | d = e ∨ d ∈ Δ} := by
      intro x hx y hy hxy
      exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
    rw [← Context.rekey_insert hf hi hU]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem ranked_inp_name {n m : Nat} {Δ : Context} {e : Key}
    {c : Capability} {s : Protocol} {p : Proc} {f : Name → Name}
    (hg : GuardMin Δ e c.rank) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .recvName s) (ha : e.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {d | d ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {d | d ∈ Δ.insert e ⟨c.rank, s⟩})
    (hu : Set.InjOn (Key.mapName (under f)) {d | d ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)})
    (hp : RankedType (m + 1)
      (Context.rekey (Key.mapName (under f)) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) hu)
      (mapProc (under f) p)) :
    RankedType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f (.inp e.name p)) := by
  apply RankedType.inpName (e := Key.mapName f e) (c := c) (s := s)
  · exact hg.rekey hf
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope _ ha
  · have hU : Set.InjOn (Key.mapName f) {d | d = e ∨ d ∈ Δ} := by
      intro x hx y hy hxy
      exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
    rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem ranked_out_endpoint {n m k : Nat} {Δ : Context} {e d : Key}
    {c : Capability} {v s : Protocol} {p : Proc} {f : Name → Name}
    (hg : GuardMin Δ e c.rank) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendEndpoint d.role k v s)
    (hd : Δ.lookup d = some ⟨k, v⟩) (hne : e ≠ d)
    (ha : e.name.ClosedAt n) (hb : d.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {a | a ∈ Δ})
    (hE : Set.InjOn (Key.mapName f) {a | a ∈ Δ.erase d})
    (hi : Set.InjOn (Key.mapName f) {a | a ∈ (Δ.erase d).insert e ⟨c.rank, s⟩})
    (hp : RankedType m
      (Context.rekey (Key.mapName f) ((Δ.erase d).insert e ⟨c.rank, s⟩) hi) (mapProc f p)) :
    RankedType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f (.out e.name d.name p)) := by
  apply RankedType.outEndpoint (e := Key.mapName f e) (d := Key.mapName f d)
    (c := c) (k := k) (t := v) (s := s)
  · exact hg.rekey hf
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact Context.lookup_rekey.mpr ⟨d, hd, rfl⟩
  · exact fun he => hne (hf (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some hd) he)
  · exact hscope _ ha
  · exact hscope _ hb
  · have hm := Finmap.mem_of_lookup_eq_some hd
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ.erase d} := by
      intro x hx y hy hxy
      exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
    rw [← Context.rekey_erase hm hf hE, ← Context.rekey_insert hE hi hU]
    exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem ranked_inp_endpoint {n m k : Nat} {Δ : Context} {e : Key}
    {c : Capability} {r : Role} {v s : Protocol} {p : Proc} {f : Name → Name}
    (hg : GuardMin Δ e c.rank) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .recvEndpoint r k v s) (ha : e.name.ClosedAt n)
    (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {a | a ∈ Δ})
    (hi : Set.InjOn (Key.mapName f) {a | a ∈ Δ.insert e ⟨c.rank, s⟩})
    (hu : Set.InjOn (Key.mapName (under f)) {a | a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)})
    (hR : Set.InjOn (Key.mapName (under f))
      {a | a ∈ (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, v⟩})
    (hp : RankedType (m + 1)
      (Context.rekey (Key.mapName (under f))
        ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, v⟩) hR)
      (mapProc (under f) p)) :
    RankedType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f (.inp e.name p)) := by
  apply RankedType.inpEndpoint (e := Key.mapName f e) (c := c) (r := r)
    (k := k) (t := v) (s := s)
  · exact hg.rekey hf
  · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
  · exact hs
  · exact hscope _ ha
  · have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} := by
      intro x hx y hy hxy
      exact hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
    have hUR : Set.InjOn (Key.mapName (under f))
        {a | a = (⟨.var 0, r⟩ : Key) ∨ a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)} := by
      intro x hx y hy hxy
      exact hR (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) hxy
    rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
    have heq := Context.rekey_insert hu hR hUR
    have hfix : Key.mapName (under f) (⟨.var 0, r⟩ : Key) = ⟨.var 0, r⟩ := rfl
    rw [hfix] at heq
    rw [← heq]
    exact hp

set_option backward.isDefEq.respectTransparency false in
/-- **Collision-free renaming preserves ranked typing.**
Physical-name rekeying preserves the entire syntax-directed refinement,
including all guard priorities, passive/endpoint payloads and nested binders.
Injectivity is needed only on owned keys, as in the base ownership judgement. -/
theorem RankedType.rename {n m : Nat} {Δ : Context} {p : Proc} {f : Name → Name}
    (h : RankedType n Δ p) (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    RankedType m (Context.rekey (Key.mapName f) Δ hf) (mapProc f p) := by
  induction h generalizing m f with
  | nil hc hs =>
    apply RankedType.nil (hc.rekey hf)
    intro e he
    obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
    exact hscope d.name (hs d hd)
  | @outName n Δ e c b s p hg hc hs ha hb hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    exact ranked_out_name hg hc hs ha hb hscope hf hi (ih hscope hi)
  | @inpName n Δ e c s p hg hc hs ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    exact ranked_inp_name hg hc hs ha hscope hf hi hu
      (ih (fun _ h => under_scoped hscope h) hu)
  | @outEndpoint n Δ e d c k t s p hg hc hs hd hne ha hb hp ih =>
    have hE := Context.injOn_erase hf (e := d)
    have hm : e ∈ Δ.erase d := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hE hm
    exact ranked_out_endpoint hg hc hs hd hne ha hb hscope hf hE hi (ih hscope hi)
  | @inpEndpoint n Δ e c r k t s p hg hc hs ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hR := Context.injOn_under_received hi r (⟨k, t⟩ : Capability)
    exact ranked_inp_endpoint hg hc hs ha hscope hf hi hu hR
      (ih (fun _ h => under_scoped hscope h) hR)
  | @par n Δ Θ p q hd hp hq ihp ihq =>
    have hΔ : Set.InjOn (Key.mapName f) {e | e ∈ Δ} := by
      intro x hx y hy hxy
      exact hf (Finmap.mem_union.mpr (Or.inl hx)) (Finmap.mem_union.mpr (Or.inl hy)) hxy
    have hΘ : Set.InjOn (Key.mapName f) {e | e ∈ Θ} := by
      intro x hx y hy hxy
      exact hf (Finmap.mem_union.mpr (Or.inr hx)) (Finmap.mem_union.mpr (Or.inr hy)) hxy
    rw [Context.rekey_union hΔ hΘ hf hd]
    apply RankedType.par ?_ (ihp hscope hΔ) (ihq hscope hΘ)
    apply Context.disjoint_rekey hΔ hΘ
    · intro x hx y hy hxy
      exact hf (Finmap.mem_union.mpr hx) (Finmap.mem_union.mpr hy) hxy
    · exact hd
  | @nu n Δ c p hp ih =>
    have hu := Context.injOn_under_bind hf c
    apply RankedType.nu (c := c)
    rw [← Context.rekey_bind hf hu]
    exact ih (fun _ h => under_scoped hscope h) hu

/-- **Binder lifting preserves ranked typing.**
Canonical binder lifting preserves every priority and endpoint rank. -/
theorem RankedType.lift {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) (k : Nat) :
    RankedType (n + 1) (Context.lift k Δ) (liftProc k p) := by
  have hf : Set.InjOn (Key.mapName (liftName k)) {e | e ∈ Δ} :=
    fun _ _ _ _ hxy => Key.mapName_injective (liftName_injective k) hxy
  have ht := h.rename (fun _ ha => ha.lift) hf
  simpa only [Context.lift, mapProc_liftName] using ht

end Cslib.SessionTypes.Endpoint
