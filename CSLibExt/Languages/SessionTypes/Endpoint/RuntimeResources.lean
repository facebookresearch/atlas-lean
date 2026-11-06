/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeSubstitution

/-!
# Actual completed ambient resources in runtime typing

Completed annotations do not become captured BODY capabilities. Weakening
and erasure use actual unfolded done and all-position physical-name absence.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Inserting a completed entry preserves invocation priority.**
A completed frame is ignored by shared priority, with NO active-payload exemption. -/
theorem InvocationPriority.insert_completed {sig : ServiceSignature} {Δ : Context}
    (h : InvocationPriority sig Δ) {z : Key} {u : Capability} (hu : u.protocol.unfold = .done) :
    InvocationPriority sig (Δ.insert z u) := by
  intro e c hc ha
  by_cases he : e = z
  · subst e
    rw [Finmap.lookup_insert] at hc
    cases hc
    exact False.elim (ha hu)
  · rw [Finmap.lookup_insert_of_ne _ he] at hc
    exact h e c hc ha

private theorem fresh_owned_ne {Δ : Context} {e z : Key} {c : Capability}
    (hz : z ∉ Δ) (hc : Δ.lookup e = some c) : e ≠ z := by
  intro he
  exact hz (he ▸ Finmap.mem_of_lookup_eq_some hc)

private theorem nonshared_lift {Γ : ServiceEnv} {a : Name}
    (h : ∀ s sig, Γ.lookup s = some sig → a ≠ .const s) :
    ∀ s sig, Γ.lookup s = some sig → liftName 0 a ≠ .const s := by
  intro s sig hs hn
  exact h s sig hs (liftName_injective 0 hn)

/-- **Weakening runtime typing by one fresh completed entry.**
ALL10 rules admit a fresh COMPLETED ambient annotation. Its name is scoped
and nonshared; accept/serve BODY ownership is unchanged, never captured. -/
theorem HasType.weaken_completed {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) {z : Key} {u : Capability} (hz : z ∉ Δ)
    (hu : u.protocol.unfold = .done) (hscope : z.name.ClosedAt n)
    (hshared : ∀ s sig, Γ.lookup s = some sig → z.name ≠ .const s) :
    HasType n Γ (Δ.insert z u) p := by
  induction h generalizing z u with
  | nil hc hs hsep =>
    apply HasType.nil (hc.insert hu) ?_ (hsep.insert z u hshared)
    intro e he
    rcases Finmap.mem_insert.mp he with rfl | he
    · exact hscope
    · exact hs e he
  | @outName n Γ Δ e c b s p hg hsep hc hh ha hb hp ih =>
    have hez := fresh_owned_ne hz hc
    have ht := ih (Context.fresh_insert_owned hz (Finmap.mem_of_lookup_eq_some hc))
      hu hscope hshared
    apply HasType.outName (e := e) (c := c) (s := s) (hg.insert_completed hu)
      (hsep.insert z u hshared)
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hh
    · exact ha
    · exact hb
    · rw [Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez] at ht
      exact ht
  | @inpName n Γ Δ e c s p hg hsep hc hh ha hp ih =>
    have hez := fresh_owned_ne hz hc
    have hzL := Context.fresh_lift_of_fresh
      (Context.fresh_insert_owned (c := (⟨c.rank, s⟩ : Capability))
        hz (Finmap.mem_of_lookup_eq_some hc))
    have ht := ih hzL hu ((closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope)
      (nonshared_lift hshared)
    apply HasType.inpName (e := e) (c := c) (s := s) (hg.insert_completed hu)
      (hsep.insert z u hshared)
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hh
    · exact ha
    · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez, Context.lift_insert]
      exact ht
  | @outEndpoint n Γ Δ e d c v k t s p hg hsep hc hh hd hv hne ha hb hp ih =>
    have hez := fresh_owned_ne hz hc
    have hdz := fresh_owned_ne hz hd
    have hzE : z ∉ Δ.erase d := fun hm => hz (Finmap.mem_erase.mp hm).2
    have heE := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have ht := ih (Context.fresh_insert_owned hzE heE) hu hscope hshared
    apply HasType.outEndpoint (e := e) (d := d) (c := c) (v := v) (s := s)
      (hg.insert_completed hu) (hsep.insert z u hshared)
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hh
    · rw [Finmap.lookup_insert_of_ne _ hdz]; exact hd
    · exact hv
    · exact hne
    · exact ha
    · exact hb
    · rw [Context.erase_insert_ne hdz.symm,
        ← Finmap.insert_insert_of_ne (s := Δ.erase d) (a := e) (a' := z) hez]
      exact ht
  | @inpEndpoint n Γ Δ e c r k t s p hg hsep hc hh ha hp ih =>
    have hez := fresh_owned_ne hz hc
    have hzL := Context.fresh_lift_of_fresh
      (Context.fresh_insert_owned (c := (⟨c.rank, s⟩ : Capability))
        hz (Finmap.mem_of_lookup_eq_some hc))
    have hzR : Key.mapName (liftName 0) z ∉
        (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert (⟨.var 0, r⟩ : Key) ⟨k, t⟩ := by
      intro hm
      rcases Finmap.mem_insert.mp hm with hm | hm
      · exact Key.lift_ne_bound z r hm
      · exact hzL hm
    have ht := ih hzR hu ((closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope)
      (nonshared_lift hshared)
    apply HasType.inpEndpoint (e := e) (c := c) (r := r) (k := k) (t := t) (s := s)
      (hg.insert_completed hu) (hsep.insert z u hshared)
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hh
    · exact ha
    · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez, Context.lift_insert]
      rw [Finmap.insert_insert_of_ne
        (s := Context.lift 0 (Δ.insert e ⟨c.rank, s⟩))
        (a := (⟨.var 0, r⟩ : Key)) (a' := Key.mapName (liftName 0) z)
        (Key.lift_ne_bound z r).symm] at ht
      exact ht
  | @invoke n Γ Δ s sig e v p hs hsep hv hr he hg hb hp ih =>
    have hez := fresh_owned_ne hz hv
    have hzE : z ∉ Δ.erase e := fun hm => hz (Finmap.mem_erase.mp hm).2
    have ht := ih hzE hu hscope hshared
    apply HasType.invoke hs (hsep.insert z u hshared)
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hv
    · exact hr
    · exact he
    · exact hg.insert_completed hu
    · exact hb
    · rw [Context.erase_insert_ne hez.symm]
      exact ht
  | accept hs hc hsc hsep hp ih =>
    apply HasType.accept hs (hc.insert hu) ?_ (hsep.insert z u hshared) hp
    intro e he
    rcases Finmap.mem_insert.mp he with rfl | he
    · exact hscope
    · exact hsc e he
  | serve ht hp hc hsc hsep ih =>
    apply HasType.serve ht hp (hc.insert hu) ?_ (hsep.insert z u hshared)
    intro e he
    rcases Finmap.mem_insert.mp he with rfl | he
    · exact hscope
    · exact hsc e he
  | par hd hp hq ihp ihq =>
    have hzL : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inl hm))
    have hzR : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inr hm))
    have ht := HasType.par (Context.disjoint_insert_fresh hd hzR)
      (ihp hzL hu hscope hshared) hq
    rw [← Finmap.insert_union] at ht
    exact ht
  | nu hs hp ih =>
    have ht := ih (Context.fresh_bind_of_fresh hz) hu
      ((closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope) (nonshared_lift hshared)
    rw [← Context.bind_insert] at ht
    exact HasType.nu (hs.insert z u hshared) ht

/-- **Weakening runtime typing by a disjoint completed context.**
A disjoint completed/scoped/nonshared finite ambient frame can be reattached.
The actual replica/accept BODY is not expanded by those annotations. -/
theorem HasType.weaken_completed_union {n : Nat} {Γ : ServiceEnv} {Δ Θ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (hd : Finmap.Disjoint Δ Θ) (hc : Θ.Completed)
    (hs : ∀ e ∈ Θ, e.name.ClosedAt n) (hsep : Separated Γ Θ) : HasType n Γ (Δ ∪ Θ) p := by
  classical
  revert hd hc hs hsep
  induction Θ using (measure fun Ξ : Context => Ξ.keys.card).wf.induction with
  | h Θ ih =>
    intro hd hc hs hsep
    by_cases hempty : Θ = ∅
    · subst Θ
      simpa only [Finmap.union_empty] using h
    · have hb : ∃ e c, Θ.lookup e = some c := by
        by_contra hn
        push Not at hn
        apply hempty
        apply Finmap.ext_lookup
        intro e
        cases he : Θ.lookup e with
        | none => simp only [Finmap.lookup_empty]
        | some c => exact False.elim (hn e c he)
      obtain ⟨e, c, he⟩ := hb
      have hem := Finmap.mem_of_lookup_eq_some he
      have hdE : Finmap.Disjoint Δ (Θ.erase e) := fun x hx hy => hd x hx (Finmap.mem_erase.mp hy).2
      have hsE : ∀ x ∈ Θ.erase e, x.name.ClosedAt n := fun x hx => hs x (Finmap.mem_erase.mp hx).2
      have hlt : (Θ.erase e).keys.card < Θ.keys.card := by
        rw [Finmap.keys_erase]
        exact Finset.card_erase_lt_of_mem (Finmap.mem_keys.mpr hem)
      have ht := ih (Θ.erase e) hlt hdE hc.erase hsE (hsep.erase e)
      have heD : e ∉ Δ := fun hm => hd e hm hem
      have hfresh : e ∉ Δ ∪ Θ.erase e := by
        intro hm
        rcases Finmap.mem_union.mp hm with hm | hm
        · exact heD hm
        · exact Finmap.notMem_erase_self hm
      have ht' := ht.weaken_completed hfresh (hc e c he) (hs e hem) (hsep e c he)
      have hrestore : (Θ.erase e).insert e c = Θ := by
        rw [Context.insert_erase_same, Context.insert_of_lookup he]
      rw [Context.insert_union_right_of_fresh heD, hrestore] at ht'
      exact ht'

/-- **Erasing an owned key preserves invocation priority.**
Removing an owned key preserves the shared priority inequalities on the remainder. -/
theorem InvocationPriority.erase {sig : ServiceSignature} {Δ : Context}
    (h : InvocationPriority sig Δ) (z : Key) : InvocationPriority sig (Δ.erase z) := by
  intro e c hc ha
  by_cases he : e = z
  · subst e
    rw [Finmap.lookup_erase] at hc
    cases hc
  · rw [Finmap.lookup_erase_ne he] at hc
    exact h e c hc ha

end Cslib.SessionTypes.Endpoint.Runtime
