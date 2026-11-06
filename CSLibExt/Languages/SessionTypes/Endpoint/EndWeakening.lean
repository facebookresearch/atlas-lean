/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Typing
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra

/-!
# Completed endpoint weakening for exact structural-congruence typing

Only unused completed capabilities may be added. Active capabilities cannot
be discarded, and the nil inversion theorem checks that distinction.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

private theorem weaken_outName {n : Nat} {Δ : Context} {e d : Key}
    {c u : Capability} {s : Protocol} {b : Name} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendName s)
    (ha : e.name.ClosedAt n) (hb : b.ClosedAt n) (hd : d ∉ Δ)
    (hp : HasType n ((Δ.insert e ⟨c.rank, s⟩).insert d u) p) :
    HasType n (Δ.insert d u) (.out e.name b p) := by
  have hne : e ≠ d := by
    intro h
    exact hd (h ▸ Finmap.mem_of_lookup_eq_some hc)
  apply HasType.outName
  · rw [Finmap.lookup_insert_of_ne _ hne]
    exact hc
  · exact hs
  · exact ha
  · exact hb
  · rw [Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := d) hne] at hp
    exact hp

private theorem weaken_inpName {n : Nat} {Δ : Context} {e d : Key}
    {c u : Capability} {s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvName s)
    (ha : e.name.ClosedAt n) (hd : d ∉ Δ)
    (hp : HasType (n + 1)
      ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert
        (Key.mapName (liftName 0) d) u) p) :
    HasType n (Δ.insert d u) (.inp e.name p) := by
  have hne : e ≠ d := by
    intro h
    exact hd (h ▸ Finmap.mem_of_lookup_eq_some hc)
  apply HasType.inpName
  · rw [Finmap.lookup_insert_of_ne _ hne]
    exact hc
  · exact hs
  · exact ha
  · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := d) hne,
      Context.lift_insert]
    exact hp

private theorem weaken_outEndpoint {n k : Nat} {Δ : Context} {e d z : Key}
    {c u : Capability} {t s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendEndpoint d.role k t s)
    (ht : Δ.lookup d = some ⟨k, t⟩) (hne : e ≠ d)
    (ha : e.name.ClosedAt n) (hb : d.name.ClosedAt n) (hz : z ∉ Δ)
    (hp : HasType n (((Δ.erase d).insert e ⟨c.rank, s⟩).insert z u) p) :
    HasType n (Δ.insert z u) (.out e.name d.name p) := by
  have hez : e ≠ z := by
    intro h
    exact hz (h ▸ Finmap.mem_of_lookup_eq_some hc)
  have hdz : d ≠ z := by
    intro h
    exact hz (h ▸ Finmap.mem_of_lookup_eq_some ht)
  refine HasType.outEndpoint ?_ hs ?_ hne ha hb ?_
  · rw [Finmap.lookup_insert_of_ne _ hez]
    exact hc
  · rw [Finmap.lookup_insert_of_ne _ hdz]
    exact ht
  · rw [Context.erase_insert_ne hdz.symm,
      ← Finmap.insert_insert_of_ne (s := Δ.erase d) (a := e) (a' := z) hez]
    exact hp

private theorem weaken_inpEndpoint {n k : Nat} {Δ : Context} {e z : Key}
    {c u : Capability} {r : Role} {t s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvEndpoint r k t s)
    (ha : e.name.ClosedAt n) (hz : z ∉ Δ)
    (hp : HasType (n + 1)
      (((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩).insert
        (Key.mapName (liftName 0) z) u) p) :
    HasType n (Δ.insert z u) (.inp e.name p) := by
  have hez : e ≠ z := by
    intro h
    exact hz (h ▸ Finmap.mem_of_lookup_eq_some hc)
  refine HasType.inpEndpoint ?_ hs ha ?_
  · rw [Finmap.lookup_insert_of_ne _ hez]
    exact hc
  · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez,
      Context.lift_insert]
    rw [Finmap.insert_insert_of_ne
      (s := Context.lift 0 (Δ.insert e ⟨c.rank, s⟩))
      (a := (⟨.var 0, r⟩ : Key)) (a' := Key.mapName (liftName 0) z)
      (Key.lift_ne_bound z r).symm] at hp
    exact hp

/-- **Weakening by an unused completed endpoint.**
An unused completed endpoint may be added through every current typing
constructor. Scope and freshness are explicit; active weakening is not admitted. -/
theorem HasType.weaken_completed {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) {z : Key} {u : Capability} (hz : z ∉ Δ)
    (hu : u.protocol.unfold = .done) (hscope : z.name.ClosedAt n) :
    HasType n (Δ.insert z u) p := by
  induction h generalizing z u with
  | nil hc hs => exact HasType.nil_insert (.nil hc hs) hu hscope
  | outName hc hs ha hb hp ih =>
    exact weaken_outName hc hs ha hb hz
      (ih (Context.fresh_insert_owned hz (Finmap.mem_of_lookup_eq_some hc)) hu hscope)
  | @inpName n Δ e c s p hc hs ha hp ih =>
    have hz' := Context.fresh_lift_of_fresh
      (Context.fresh_insert_owned (c := (⟨c.rank, s⟩ : Capability))
        hz (Finmap.mem_of_lookup_eq_some hc))
    have hscope' := (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope
    exact weaken_inpName hc hs ha hz (ih hz' hu hscope')
  | @outEndpoint n Δ e d c k t s p hc hs ht hne ha hb hp ih =>
    have hzE : z ∉ Δ.erase d := fun hm => hz (Finmap.mem_erase.mp hm).2
    have heE := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    exact weaken_outEndpoint hc hs ht hne ha hb hz
      (ih (Context.fresh_insert_owned hzE heE) hu hscope)
  | @inpEndpoint n Δ e c r k t s p hc hs ha hp ih =>
    have hzL := Context.fresh_lift_of_fresh
      (Context.fresh_insert_owned (c := (⟨c.rank, s⟩ : Capability))
        hz (Finmap.mem_of_lookup_eq_some hc))
    have hzI : Key.mapName (liftName 0) z ∉
        (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert
          (⟨.var 0, r⟩ : Key) ⟨k, t⟩ := by
      intro hm
      rcases Finmap.mem_insert.mp hm with hm | hm
      · exact Key.lift_ne_bound z r hm
      · exact hzL hm
    have hscope' := (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope
    exact weaken_inpEndpoint hc hs ha hz (ih hzI hu hscope')
  | par hd hp hq ihp ihq =>
    have hzL : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inl hm))
    have hzR : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inr hm))
    have ht := HasType.par (Context.disjoint_insert_fresh hd hzR)
      (ihp hzL hu hscope) hq
    rw [← Finmap.insert_union] at ht
    exact ht
  | nu hp ih =>
    have hscope' := (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope
    have ht := ih (Context.fresh_bind_of_fresh hz) hu hscope'
    rw [← Context.bind_insert] at ht
    exact HasType.nu ht

/-- **Weakening by a disjoint completed context.**
A disjoint completed context can be reattached to any typed process,
with the exact finite-map union required by parallel-nil congruence. -/
theorem HasType.weaken_completed_union {n : Nat} {Δ Θ : Context} {p : Proc}
    (h : HasType n Δ p) (hd : Finmap.Disjoint Δ Θ) (hc : Θ.Completed)
    (hs : ∀ e ∈ Θ, e.name.ClosedAt n) : HasType n (Δ ∪ Θ) p := by
  classical
  revert hd hc hs
  induction Θ using (measure fun Γ : Context => Γ.keys.card).wf.induction with
  | h Θ ih =>
    intro hd hc hs
    by_cases hEmpty : Θ = ∅
    · subst Θ
      simpa only [Finmap.union_empty] using h
    · have hbinding : ∃ e c, Θ.lookup e = some c := by
        by_contra hn
        push Not at hn
        apply hEmpty
        apply Finmap.ext_lookup
        intro e
        cases he : Θ.lookup e with
        | none => simp only [Finmap.lookup_empty]
        | some c => exact False.elim (hn e c he)
      obtain ⟨e, c, he⟩ := hbinding
      have hem := Finmap.mem_of_lookup_eq_some he
      have hdE : Finmap.Disjoint Δ (Θ.erase e) :=
        fun x hx hy => hd x hx (Finmap.mem_erase.mp hy).2
      have hsE : ∀ x ∈ Θ.erase e, x.name.ClosedAt n :=
        fun x hx => hs x (Finmap.mem_erase.mp hx).2
      have hlt : (Θ.erase e).keys.card < Θ.keys.card := by
        rw [Finmap.keys_erase]
        exact Finset.card_erase_lt_of_mem (Finmap.mem_keys.mpr hem)
      have ht := ih (Θ.erase e) hlt hdE hc.erase hsE
      have heD : e ∉ Δ := fun hm => hd e hm hem
      have heFresh : e ∉ Δ ∪ Θ.erase e := by
        intro hm
        rcases Finmap.mem_union.mp hm with hm | hm
        · exact heD hm
        · exact Finmap.notMem_erase_self hm
      have ht' := ht.weaken_completed heFresh (hc e c he) (hs e hem)
      have hrestore : (Θ.erase e).insert e c = Θ := by
        calc
          (Θ.erase e).insert e c = ((Θ.erase e) ∪ ∅).insert e c := by
            rw [Finmap.union_empty]
          _ = Θ.erase e ∪ (∅ : Context).insert e c :=
            Context.insert_union_right_of_fresh Finmap.notMem_erase_self
          _ = Θ ∪ ∅ := Context.transfer_union he
          _ = Θ := Finmap.union_empty
      rw [Context.insert_union_right_of_fresh heD, hrestore] at ht'
      exact ht'

/-- **Removing a parallel nil preserves endpoint typing.**
Removing a parallel nil reattaches exactly its completed ownership;
no active capability is silently dropped. -/
theorem HasType.par_nil_elim {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ (.par p .nil)) : HasType n Δ p := by
  obtain ⟨Θ, Ξ, rfl, hd, hp, hnil⟩ := h.par_inv
  exact hp.weaken_completed_union hd hnil.nil_inv.1 hnil.nil_inv.2

end Cslib.SessionTypes.Endpoint
