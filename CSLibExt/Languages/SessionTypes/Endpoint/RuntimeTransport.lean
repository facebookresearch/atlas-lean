/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeNames
public import CSLibExt.Languages.SessionTypes.Endpoint.SwapTyping

/-!
# General Γ-preserving runtime name transport

Owned-key injectivity, canonical scope, fixed declared constants and actual
owned-image nonalias are static premises. No ready/Step/representative field
is used; replication BODY transport remains at EMPTY ownership.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

set_option backward.isDefEq.respectTransparency false in
/-- **Runtime typing under renamings that fix and avoid shared names.**
ALL10 runtime derivation rules transport actual names with Γ unchanged.
Shared nonalias is required only on OWNED images, not unrestricted passive names. -/
theorem HasType.rename {n m : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc} {f : Name → Name}
    (h : HasType n Γ Δ p) (hscope : ∀ a, a.ClosedAt n → (f a).ClosedAt m)
    (hfix : FixesShared Γ f) (hn : NonAliases Γ Δ f)
    (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    HasType m Γ (Context.rekey (Key.mapName f) Δ hf) (mapProc f p) := by
  induction h generalizing m f with
  | nil hc hs hsep =>
    apply HasType.nil (hc.rekey hf) ?_ (hn.separated hf)
    intro e he
    obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
    exact hscope d.name (hs d hd)
  | @outName n Γ Δ e c b s p hg hsep hc hh ha hb hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply HasType.outName (e := Key.mapName f e) (c := c) (s := s) (hg.rekey hf)
      (hn.separated hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · exact hscope _ hb
    · rw [← Context.rekey_insert hf hi hU]
      exact ih hscope hfix (hn.insert_owned (Finmap.mem_of_lookup_eq_some hc) _) hi
  | @inpName n Γ Δ e c s p hg hsep hc hh ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply HasType.inpName (e := Key.mapName f e) (c := c) (s := s) (hg.rekey hf)
      (hn.separated hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
      exact ih (fun _ ha => under_scoped hscope ha) hfix.under
        (hn.insert_owned (Finmap.mem_of_lookup_eq_some hc) _).under_lift hu
  | @outEndpoint n Γ Δ e d c v k t s p hg hsep hc hh hv he hne ha hb hp ih =>
    have hE := Context.injOn_erase hf (e := d)
    have hm : e ∈ Δ.erase d := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hE hm
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ.erase d} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply HasType.outEndpoint (e := Key.mapName f e) (d := Key.mapName f d)
      (c := c) (v := v) (k := k) (t := t) (s := s) (hg.rekey hf) (hn.separated hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact Context.lookup_rekey.mpr ⟨d, hv, rfl⟩
    · exact he
    · intro heq
      exact hne (hf (Finmap.mem_of_lookup_eq_some hc) (Finmap.mem_of_lookup_eq_some hv) heq)
    · exact hscope _ ha
    · exact hscope _ hb
    · rw [← Context.rekey_erase (Finmap.mem_of_lookup_eq_some hv) hf hE,
        ← Context.rekey_insert hE hi hU]
      exact ih hscope hfix ((hn.erase d).insert_owned hm _) hi
  | @inpEndpoint n Γ Δ e c r k t s p hg hsep hc hh ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hR := Context.injOn_under_received hi r (⟨k, t⟩ : Capability)
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    have hUR : Set.InjOn (Key.mapName (under f))
        {a | a = (⟨.var 0, r⟩ : Key) ∨ a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)} :=
      fun _ hx _ hy he => hR (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply HasType.inpEndpoint (e := Key.mapName f e) (c := c) (r := r)
      (k := k) (t := t) (s := s) (hg.rekey hf) (hn.separated hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
      have heq := Context.rekey_insert hu hR hUR
      have hzero : Key.mapName (under f) (⟨.var 0, r⟩ : Key) = ⟨.var 0, r⟩ := rfl
      rw [hzero] at heq
      rw [← heq]
      exact ih (fun _ ha => under_scoped hscope ha) hfix.under
        ((hn.insert_owned (Finmap.mem_of_lookup_eq_some hc) _).under_received r ⟨k, t⟩) hR
  | @invoke n Γ Δ s sig e v p hs hsep hv hr he hg hb hp ih =>
    have hE := Context.injOn_erase hf (e := e)
    have hnew : HasType m Γ (Context.rekey (Key.mapName f) (Δ.erase e) hE) (mapProc f p) :=
      ih hscope hfix (hn.erase e) hE
    rw [Context.rekey_erase (Finmap.mem_of_lookup_eq_some hv) hf hE] at hnew
    simpa only [mapProc, hfix s sig hs, Key.mapName] using
      HasType.invoke hs (hn.separated hf) (Context.lookup_rekey.mpr ⟨e, hv, rfl⟩)
        hr he (hg.rekey hf) (hscope _ hb) hnew
  | @accept n Γ Δ s sig p hs hc hsc hsep hp ih =>
    have hR : Set.InjOn (Key.mapName (under f))
        {e | e ∈ (Finmap.singleton (⟨.var 0, sig.role⟩ : Key) sig.capability : Context)} := by
      intro x hx y hy he
      exact ((Finmap.mem_singleton _ _ _).mp hx).trans ((Finmap.mem_singleton _ _ _).mp hy).symm
    have hN : NonAliases Γ (Finmap.singleton (⟨.var 0, sig.role⟩ : Key) sig.capability)
        (under f) := by
      intro e he s sig hs hn
      have hz := (Finmap.mem_singleton _ _ _).mp he
      subst e
      cases hn
    have hb := ih (fun _ ha => under_scoped hscope ha) hfix.under hN hR
    rw [rekey_singleton] at hb
    simpa only [mapProc, hfix s sig hs, Key.mapName] using HasType.accept hs (hc.rekey hf)
      (fun e he => by
        obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
        exact hscope _ (hsc d hd)) (hn.separated hf) hb
  | @serve n Γ Δ p ht hp hc hsc hsep ih =>
    have hE : Set.InjOn (Key.mapName f) {e | e ∈ (∅ : Context)} :=
      fun _ hx => False.elim (Finmap.notMem_empty hx)
    have hb := ih hscope hfix (nonaliases_empty Γ f) hE
    rw [rekey_empty] at hb
    exact HasType.serve (ht.rename hfix) hb (hc.rekey hf)
      (fun e he => by
        obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
        exact hscope _ (hsc d hd)) (hn.separated hf)
  | @par n Γ Δ Θ p q hd hp hq ihp ihq =>
    have hΔ : Set.InjOn (Key.mapName f) {e | e ∈ Δ} :=
      fun _ hx _ hy he => hf (Finmap.mem_union.mpr (Or.inl hx))
        (Finmap.mem_union.mpr (Or.inl hy)) he
    have hΘ : Set.InjOn (Key.mapName f) {e | e ∈ Θ} :=
      fun _ hx _ hy he => hf (Finmap.mem_union.mpr (Or.inr hx))
        (Finmap.mem_union.mpr (Or.inr hy)) he
    rw [Context.rekey_union hΔ hΘ hf hd]
    apply HasType.par ?_ (ihp hscope hfix hn.union_left hΔ) (ihq hscope hfix hn.union_right hΘ)
    apply Context.disjoint_rekey hΔ hΘ
    · intro x hx y hy he
      exact hf (Finmap.mem_union.mpr hx) (Finmap.mem_union.mpr hy) he
    · exact hd
  | @nu n Γ Δ c p hs hp ih =>
    have hu := Context.injOn_under_bind hf c
    apply HasType.nu (c := c) (hn.separated hf)
    rw [← Context.rekey_bind hf hu]
    exact ih (fun _ ha => under_scoped hscope ha) hfix.under (hn.under_bind c) hu

/-- **Binder lifting preserves runtime typing.**
Canonical binder lift retains the entire runtime derivation and Γ literally. -/
theorem HasType.lift {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (k : Nat) : HasType (n + 1) Γ (Context.lift k Δ) (liftProc k p) := by
  have hi : Set.InjOn (Key.mapName (liftName k)) {e | e ∈ Δ} :=
    fun _ _ _ _ he => Key.mapName_injective (liftName_injective k) he
  simpa only [Context.lift, mapProc_liftName] using
    h.rename (fun _ ha => ha.lift) (fun _ _ _ => rfl) (h.separated.nonaliases_lift k) hi

/-- **Binder swapping preserves runtime typing.**
Canonical swap permutes actual owned binders without changing Γ or cap metadata. -/
theorem HasType.swap {n k : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (hk : k + 1 < n) : HasType n Γ (Context.swap k Δ) (swapProc k p) := by
  have hi : Set.InjOn (Key.mapName (swapNameAt k)) {e | e ∈ Δ} :=
    fun _ _ _ _ he => Key.mapName_injective (swapNameAt_injective k) he
  simpa only [Context.swap, mapProc_swapNameAt] using
    h.rename (fun a ha => (closedAt_swapName_iff n k hk a).mpr ha)
      (fun _ _ _ => rfl) (h.separated.nonaliases_swap k) hi

end Cslib.SessionTypes.Endpoint.Runtime
