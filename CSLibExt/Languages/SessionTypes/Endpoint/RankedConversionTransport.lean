/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionRetyping
public import CSLibExt.Languages.SessionTypes.Endpoint.TypingTransport
public import CSLibExt.Languages.SessionTypes.Endpoint.SwapTyping

/-!
# Capture-safe static-priority conversion typing transport

The seven-rule proof uses existing key/map equations at their actual types,
not an old RankedType theorem applied to a new judgement.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

set_option backward.isDefEq.respectTransparency false in
/-- **Collision-free renaming preserves conversion ranked typing.**
GENERAL name transport with collision freedom on actual owned keys and
canonical ambient name scope; protocol codes, roles and ranks stay exact. -/
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
  | @outName n Δ e c b s p hg hc hh ha hb hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply RankedType.outName (e := Key.mapName f e) (c := c) (s := s) (hg.rekey hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · exact hscope _ hb
    · rw [← Context.rekey_insert hf hi hU]
      exact ih hscope hi
  | @inpName n Δ e c s p hg hc hh ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply RankedType.inpName (e := Key.mapName f e) (c := c) (s := s) (hg.rekey hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
      exact ih (fun _ ha => under_scoped hscope ha) hu
  | @outEndpoint n Δ e d c v k t s p hg hc hh hv he hne ha hb hp ih =>
    have hE := Context.injOn_erase hf (e := d)
    have hm : e ∈ Δ.erase d := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hE hm
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ.erase d} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply RankedType.outEndpoint (e := Key.mapName f e) (d := Key.mapName f d)
      (c := c) (v := v) (k := k) (t := t) (s := s) (hg.rekey hf)
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
      exact ih hscope hi
  | @inpEndpoint n Δ e c r k t s p hg hc hh ha hp ih =>
    have hi := Context.injOn_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hf
      (Finmap.mem_of_lookup_eq_some hc)
    have hu := Context.injOn_under_lift hi
    have hR := Context.injOn_under_received hi r (⟨k, t⟩ : Capability)
    have hU : Set.InjOn (Key.mapName f) {a | a = e ∨ a ∈ Δ} :=
      fun _ hx _ hy he => hi (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    have hUR : Set.InjOn (Key.mapName (under f))
        {a | a = (⟨.var 0, r⟩ : Key) ∨ a ∈ Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)} :=
      fun _ hx _ hy he => hR (Finmap.mem_insert.mpr hx) (Finmap.mem_insert.mpr hy) he
    apply RankedType.inpEndpoint (e := Key.mapName f e) (c := c) (r := r)
      (k := k) (t := t) (s := s) (hg.rekey hf)
    · exact Context.lookup_rekey.mpr ⟨e, hc, rfl⟩
    · exact hh
    · exact hscope _ ha
    · rw [← Context.rekey_insert hf hi hU, ← Context.rekey_under_lift hi hu]
      have heq := Context.rekey_insert hu hR hUR
      have hfix : Key.mapName (under f) (⟨.var 0, r⟩ : Key) = ⟨.var 0, r⟩ := rfl
      rw [hfix] at heq
      rw [← heq]
      exact ih (fun _ ha => under_scoped hscope ha) hR
  | @par n Δ Θ p q hd hp hq ihp ihq =>
    have hΔ : Set.InjOn (Key.mapName f) {e | e ∈ Δ} :=
      fun _ hx _ hy he => hf (Finmap.mem_union.mpr (Or.inl hx))
        (Finmap.mem_union.mpr (Or.inl hy)) he
    have hΘ : Set.InjOn (Key.mapName f) {e | e ∈ Θ} :=
      fun _ hx _ hy he => hf (Finmap.mem_union.mpr (Or.inr hx))
        (Finmap.mem_union.mpr (Or.inr hy)) he
    rw [Context.rekey_union hΔ hΘ hf hd]
    apply RankedType.par ?_ (ihp hscope hΔ) (ihq hscope hΘ)
    apply Context.disjoint_rekey hΔ hΘ
    · intro x hx y hy he
      exact hf (Finmap.mem_union.mpr hx) (Finmap.mem_union.mpr hy) he
    · exact hd
  | @nu n Δ c p hp ih =>
    have hu := Context.injOn_under_bind hf c
    apply RankedType.nu (c := c)
    rw [← Context.rekey_bind hf hu]
    exact ih (fun _ ha => under_scoped hscope ha) hu

/-- **Binder lifting preserves conversion ranked typing.**
Lift uses the canonical cutoff-aware name and process operations. -/
theorem RankedType.lift {n : Nat} {Δ : Context} {p : Proc} (h : RankedType n Δ p) (k : Nat) :
    RankedType (n + 1) (Context.lift k Δ) (liftProc k p) := by
  have hi : Set.InjOn (Key.mapName (liftName k)) {e | e ∈ Δ} :=
    fun _ _ _ _ he => Key.mapName_injective (liftName_injective k) he
  simpa only [Context.lift, mapProc_liftName] using h.rename (fun _ ha => ha.lift) hi

/-- **Binder swap preserves conversion ranked typing.**
Swap retains roles, protocols and ranks while permuting two ambient binders. -/
theorem RankedType.swap {n k : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) (hk : k + 1 < n) :
    RankedType n (Context.swap k Δ) (swapProc k p) := by
  have hi : Set.InjOn (Key.mapName (swapNameAt k)) {e | e ∈ Δ} :=
    fun _ _ _ _ he => Key.mapName_injective (swapNameAt_injective k) he
  simpa only [Context.swap, mapProc_swapNameAt] using
    h.rename (fun a ha => (closedAt_swapName_iff n k hk a).mpr ha) hi

end Cslib.SessionTypes.Endpoint.Conversion
