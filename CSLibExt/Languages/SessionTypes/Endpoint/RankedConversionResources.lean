/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionSubstitution
public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionResources
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedResources

/-!
# Completed ownership transport for ranked conversion typing
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

private theorem fresh_owned_ne {Δ : Context} {e z : Key} {c : Capability}
    (hz : z ∉ Δ) (hc : Δ.lookup e = some c) : e ≠ z := by
  intro he
  exact hz (he ▸ Finmap.mem_of_lookup_eq_some hc)

/-- **Weakening conversion ranked typing by a completed capability.**
Adding a fresh completed capability preserves every guard inequality
through all seven rules. No active capability can be added by this theorem. -/
theorem RankedType.weaken_completed {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) {z : Key} {u : Capability} (hz : z ∉ Δ)
    (hu : u.protocol.unfold = .done) (hscope : z.name.ClosedAt n) :
    RankedType n (Δ.insert z u) p := by
  induction h generalizing z u with
  | nil hc hs =>
    apply RankedType.nil (hc.insert hu)
    intro e he
    rcases Finmap.mem_insert.mp he with rfl | he
    · exact hscope
    · exact hs e he
  | @outName n Δ e c b s p hg hc hs ha hb hp ih =>
    have hez := fresh_owned_ne hz hc
    have ht := ih (Context.fresh_insert_owned hz (Finmap.mem_of_lookup_eq_some hc)) hu hscope
    apply RankedType.outName (e := e) (c := c) (s := s)
    · exact hg.insert_completed hu
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hs
    · exact ha
    · exact hb
    · rw [Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez] at ht
      exact ht
  | @inpName n Δ e c s p hg hc hs ha hp ih =>
    have hez := fresh_owned_ne hz hc
    have hzL := Context.fresh_lift_of_fresh
      (Context.fresh_insert_owned (c := (⟨c.rank, s⟩ : Capability))
        hz (Finmap.mem_of_lookup_eq_some hc))
    have ht := ih hzL hu ((closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope)
    apply RankedType.inpName (e := e) (c := c) (s := s)
    · exact hg.insert_completed hu
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hs
    · exact ha
    · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez,
        Context.lift_insert]
      exact ht
  | @outEndpoint n Δ e d c v k t s p hg hc hs hd hv hne ha hb hp ih =>
    have hez := fresh_owned_ne hz hc
    have hdz := fresh_owned_ne hz hd
    have hzE : z ∉ Δ.erase d := fun hm => hz (Finmap.mem_erase.mp hm).2
    have heE := Finmap.mem_erase.mpr ⟨hne, Finmap.mem_of_lookup_eq_some hc⟩
    have ht := ih (Context.fresh_insert_owned hzE heE) hu hscope
    apply RankedType.outEndpoint (e := e) (d := d) (c := c) (s := s)
    · exact hg.insert_completed hu
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hs
    · rw [Finmap.lookup_insert_of_ne _ hdz]; exact hd
    · exact hv
    · exact hne
    · exact ha
    · exact hb
    · rw [Context.erase_insert_ne hdz.symm,
        ← Finmap.insert_insert_of_ne (s := Δ.erase d) (a := e) (a' := z) hez]
      exact ht
  | @inpEndpoint n Δ e c r k t s p hg hc hs ha hp ih =>
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
    apply RankedType.inpEndpoint (e := e) (c := c) (r := r) (k := k) (t := t) (s := s)
    · exact hg.insert_completed hu
    · rw [Finmap.lookup_insert_of_ne _ hez]; exact hc
    · exact hs
    · exact ha
    · rw [← Finmap.insert_insert_of_ne (s := Δ) (a := e) (a' := z) hez, Context.lift_insert]
      rw [Finmap.insert_insert_of_ne
        (s := Context.lift 0 (Δ.insert e ⟨c.rank, s⟩))
        (a := (⟨.var 0, r⟩ : Key)) (a' := Key.mapName (liftName 0) z)
        (Key.lift_ne_bound z r).symm] at ht
      exact ht
  | par hd hp hq ihp ihq =>
    have hzL : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inl hm))
    have hzR : z ∉ _ := fun hm => hz (Finmap.mem_union.mpr (Or.inr hm))
    have ht := RankedType.par (Context.disjoint_insert_fresh hd hzR)
      (ihp hzL hu hscope) hq
    rw [← Finmap.insert_union] at ht
    exact ht
  | nu hp ih =>
    have ht := ih (Context.fresh_bind_of_fresh hz) hu
      ((closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mpr hscope)
    rw [← Context.bind_insert] at ht
    exact RankedType.nu ht

/-- **Erasing a key whose name is absent preserves conversion ranked typing.**
Actual all-position physical-name absence permits erasure in the
refinement too. Subject and payload lookup obligations are never discarded. -/
theorem RankedType.erase_nameAbsent {n : Nat} {Δ : Context} {p : Proc}
    (h : RankedType n Δ p) {z : Key} (hab : NameAbsent z.name p) :
    RankedType n (Δ.erase z) p := by
  induction h generalizing z with
  | nil hc hs => exact RankedType.nil hc.erase (fun e he => hs e (Finmap.mem_erase.mp he).2)
  | @outName n Δ e c b s p hg hc hs ha hb hp ih =>
    have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
    apply RankedType.outName (e := e) (c := c) (s := s) hg.erase
    · rw [Finmap.lookup_erase_ne hez]; exact hc
    · exact hs
    · exact ha
    · exact hb
    · have ht := ih hab.2.2
      rw [Context.erase_insert_ne hez] at ht
      exact ht
  | @inpName n Δ e c s p hg hc hs ha hp ih =>
    by_cases hm : z ∈ Δ
    · have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
      apply RankedType.inpName (e := e) (c := c) (s := s) hg.erase
      · rw [Finmap.lookup_erase_ne hez]; exact hc
      · exact hs
      · exact ha
      · have ht := ih (z := Key.mapName (liftName 0) z) hab.2
        rw [← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
          Context.erase_insert_ne hez] at ht
        exact ht
    · rw [Context.erase_of_notMem hm]
      exact RankedType.inpName hg hc hs ha hp
  | @outEndpoint n Δ e d c v k t s p hg hc hs hd hv hne ha hb hp ih =>
    have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
    have hdz : d ≠ z := fun he => hab.2.1 (congrArg Key.name he.symm)
    apply RankedType.outEndpoint (e := e) (d := d) (c := c) (s := s) hg.erase
    · rw [Finmap.lookup_erase_ne hez]; exact hc
    · exact hs
    · rw [Finmap.lookup_erase_ne hdz]; exact hd
    · exact hv
    · exact hne
    · exact ha
    · exact hb
    · have ht := ih hab.2.2
      rw [Context.erase_insert_ne hez, Finmap.erase_erase] at ht
      exact ht
  | @inpEndpoint n Δ e c r k t s p hg hc hs ha hp ih =>
    by_cases hm : z ∈ Δ
    · have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
      apply RankedType.inpEndpoint (e := e) (c := c) (r := r) (k := k) (t := t) (s := s) hg.erase
      · rw [Finmap.lookup_erase_ne hez]; exact hc
      · exact hs
      · exact ha
      · have ht := ih (z := Key.mapName (liftName 0) z) hab.2
        rw [Context.erase_insert_ne (Key.lift_ne_bound z r).symm,
          ← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
          Context.erase_insert_ne hez] at ht
        exact ht
    · rw [Context.erase_of_notMem hm]
      exact RankedType.inpEndpoint hg hc hs ha hp
  | par hd hp hq ihp ihq =>
    rw [Context.erase_union]
    exact RankedType.par
      (fun e he ht => hd e (Finmap.mem_erase.mp he).2 (Finmap.mem_erase.mp ht).2)
      (ihp hab.1) (ihq hab.2)
  | @nu n Δ c p hp ih =>
    by_cases hm : z ∈ Δ
    · have ht := ih (z := Key.mapName (liftName 0) z) hab
      rw [Context.bind_erase c hm] at ht
      exact RankedType.nu ht
    · rw [Context.erase_of_notMem hm]
      exact RankedType.nu hp

/-- **Weakening conversion ranked typing by a disjoint completed context.**
Reattaching a disjoint completed finite context preserves all guards. -/
theorem RankedType.weaken_completed_union {n : Nat} {Δ Θ : Context} {p : Proc}
    (h : RankedType n Δ p) (hd : Finmap.Disjoint Δ Θ) (hc : Θ.Completed)
    (hs : ∀ e ∈ Θ, e.name.ClosedAt n) : RankedType n (Δ ∪ Θ) p := by
  classical
  revert hd hc hs
  induction Θ using (measure fun Γ : Context => Γ.keys.card).wf.induction with
  | h Θ ih =>
    intro hd hc hs
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
      have ht := ih (Θ.erase e) hlt hdE hc.erase hsE
      have heD : e ∉ Δ := fun hm => hd e hm hem
      have hfresh : e ∉ Δ ∪ Θ.erase e := by
        intro hm
        rcases Finmap.mem_union.mp hm with hm | hm
        · exact heD hm
        · exact Finmap.notMem_erase_self hm
      have ht' := ht.weaken_completed hfresh (hc e c he) (hs e hem)
      have hrestore : (Θ.erase e).insert e c = Θ := by
        rw [Context.insert_erase_same, Context.insert_of_lookup he]
      rw [Context.insert_union_right_of_fresh heD, hrestore] at ht'
      exact ht'

end Cslib.SessionTypes.Endpoint.Conversion
