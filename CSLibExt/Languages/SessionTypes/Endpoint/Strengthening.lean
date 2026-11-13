/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.NameAbsence
public import CSLibExt.Languages.SessionTypes.Endpoint.Typing
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra

/-!
# Ownership erasure under actual all-position physical-name absence
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

private theorem erase_outName {n : Nat} {Δ : Context} {e z : Key}
    {c : Capability} {s : Protocol} {b : Name} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendName s)
    (ha : e.name.ClosedAt n) (hb : b.ClosedAt n)
    (hz : z.name ≠ e.name)
    (hp : HasType n ((Δ.insert e ⟨c.rank, s⟩).erase z) p) :
    HasType n (Δ.erase z) (.out e.name b p) := by
  have hez : e ≠ z := fun h => hz (congrArg Key.name h.symm)
  refine HasType.outName ?_ hs ha hb ?_
  · rw [Finmap.lookup_erase_ne hez]
    exact hc
  · rw [Context.erase_insert_ne hez] at hp
    exact hp

private theorem erase_inpName {n : Nat} {Δ : Context} {e z : Key}
    {c : Capability} {s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvName s)
    (ha : e.name.ClosedAt n) (hz : z.name ≠ e.name) (hm : z ∈ Δ)
    (hp : HasType (n + 1)
      ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).erase
        (Key.mapName (liftName 0) z)) p) :
    HasType n (Δ.erase z) (.inp e.name p) := by
  have hez : e ≠ z := fun h => hz (congrArg Key.name h.symm)
  refine HasType.inpName ?_ hs ha ?_
  · rw [Finmap.lookup_erase_ne hez]
    exact hc
  · rw [← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
      Context.erase_insert_ne hez] at hp
    exact hp

private theorem erase_outEndpoint {n k : Nat} {Δ : Context} {e d z : Key}
    {c : Capability} {t s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .sendEndpoint d.role k t s)
    (hd : Δ.lookup d = some ⟨k, t⟩) (hne : e ≠ d)
    (ha : e.name.ClosedAt n) (hb : d.name.ClosedAt n)
    (hz : z.name ≠ e.name) (hzd : z.name ≠ d.name)
    (hp : HasType n (((Δ.erase d).insert e ⟨c.rank, s⟩).erase z) p) :
    HasType n (Δ.erase z) (.out e.name d.name p) := by
  have hez : e ≠ z := fun h => hz (congrArg Key.name h.symm)
  have hdz : d ≠ z := fun h => hzd (congrArg Key.name h.symm)
  refine HasType.outEndpoint ?_ hs ?_ hne ha hb ?_
  · rw [Finmap.lookup_erase_ne hez]
    exact hc
  · rw [Finmap.lookup_erase_ne hdz]
    exact hd
  · rw [Context.erase_insert_ne hez, Finmap.erase_erase] at hp
    exact hp

private theorem erase_inpEndpoint {n k : Nat} {Δ : Context} {e z : Key}
    {c : Capability} {r : Role} {t s : Protocol} {p : Proc}
    (hc : Δ.lookup e = some c) (hs : c.protocol.unfold = .recvEndpoint r k t s)
    (ha : e.name.ClosedAt n) (hz : z.name ≠ e.name) (hm : z ∈ Δ)
    (hp : HasType (n + 1)
      (((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩).erase
        (Key.mapName (liftName 0) z)) p) :
    HasType n (Δ.erase z) (.inp e.name p) := by
  have hez : e ≠ z := fun h => hz (congrArg Key.name h.symm)
  refine HasType.inpEndpoint ?_ hs ha ?_
  · rw [Finmap.lookup_erase_ne hez]
    exact hc
  · rw [Context.erase_insert_ne (Key.lift_ne_bound z r).symm,
      ← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
      Context.erase_insert_ne hez] at hp
    exact hp

/-- A role can be erased when its physical name is absent from every
subject, payload and binder-adjusted continuation position of the typed term. -/
theorem HasType.erase_nameAbsent {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) {z : Key} (hab : NameAbsent z.name p) :
    HasType n (Δ.erase z) p := by
  induction h generalizing z with
  | nil hc hs =>
    exact HasType.nil hc.erase (fun e he => hs e (Finmap.mem_erase.mp he).2)
  | outName hc hs ha hb hp ih =>
    exact erase_outName hc hs ha hb hab.1 (ih hab.2.2)
  | @inpName n Δ e c s p hc hs ha hp ih =>
    by_cases hm : z ∈ Δ
    · exact erase_inpName hc hs ha hab.1 hm (ih hab.2)
    · rw [Context.erase_of_notMem hm]
      exact HasType.inpName hc hs ha hp
  | outEndpoint hc hs hd hne ha hb hp ih =>
    exact erase_outEndpoint hc hs hd hne ha hb hab.1 hab.2.1 (ih hab.2.2)
  | @inpEndpoint n Δ e c r k t s p hc hs ha hp ih =>
    by_cases hm : z ∈ Δ
    · exact erase_inpEndpoint hc hs ha hab.1 hm (ih hab.2)
    · rw [Context.erase_of_notMem hm]
      exact HasType.inpEndpoint hc hs ha hp
  | @par n Δ Θ p q hd hp hq ihp ihq =>
    have hdE : Finmap.Disjoint (Δ.erase z) (Θ.erase z) :=
      fun e he ht => hd e (Finmap.mem_erase.mp he).2 (Finmap.mem_erase.mp ht).2
    rw [Context.erase_union]
    exact HasType.par hdE (ihp hab.1) (ihq hab.2)
  | @nu n Δ c p hp ih =>
    by_cases hm : z ∈ Δ
    · have ht := ih (z := Key.mapName (liftName 0) z) hab
      rw [Context.bind_erase c hm] at ht
      exact HasType.nu ht
    · rw [Context.erase_of_notMem hm]
      exact HasType.nu hp

/-- An owned capability with no physical-name occurrence must already be
completed. This is derived from typing, including endpoint payload positions. -/
theorem HasType.absent_lookup_completed {n : Nat} {Δ : Context} {p : Proc}
    (h : HasType n Δ p) {z : Key} {t : Capability}
    (hz : Δ.lookup z = some t) (hab : NameAbsent z.name p) :
    t.protocol.unfold = .done := by
  induction h generalizing z t with
  | nil hc hs => exact hc z t hz
  | @outName n Δ e c b s p hc hs ha hb hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := z) (t := t) ?_ hab.2.2
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | @inpName n Δ e c s p hc hs ha hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab.2
    apply Context.lookup_lift.mpr
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | @outEndpoint n Δ e d c k v s p hc hs hd hne ha hb hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    have hzd : z ≠ d := fun h => hab.2.1 (congrArg Key.name h)
    apply ih (z := z) (t := t) ?_ hab.2.2
    rw [Finmap.lookup_insert_of_ne _ hze, Finmap.lookup_erase_ne hzd]
    exact hz
  | @inpEndpoint n Δ e c r k v s p hc hs ha hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab.2
    rw [Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z r)]
    apply Context.lookup_lift.mpr
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | @par n Δ Θ p q hd hp hq ihp ihq =>
    by_cases hm : z ∈ Δ
    · rw [Finmap.lookup_union_left hm] at hz
      exact ihp hz hab.1
    · rw [Finmap.lookup_union_right hm] at hz
      exact ihq hz hab.2
  | @nu n Δ c p hp ih =>
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab
    rw [Context.bind,
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .negative),
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .positive)]
    exact Context.lookup_lift.mpr hz

end Cslib.SessionTypes.Endpoint
