/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeResources
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedResources

/-!
# Runtime ownership and actual all-position name absence
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- An owned name absent from ALL subject/payload/binder-adjusted positions
already has an actual done unfolding, including in the shared runtime rules. -/
theorem HasType.absent_lookup_completed {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) {z : Key} {t : Capability}
    (hz : Δ.lookup z = some t) (hab : NameAbsent z.name p) : t.protocol.unfold = .done := by
  induction h generalizing z t with
  | nil hc hs hd => exact hc z t hz
  | @outName n Γ Δ e c b s p hg hd hc hh ha hb hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := z) (t := t) ?_ hab.2.2
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | @inpName n Γ Δ e c s p hg hd hc hh ha hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab.2
    apply Context.lookup_lift.mpr
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | @outEndpoint n Γ Δ e d c owned k v s p hg hd hc hh hv he hne ha hb hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    have hzd : z ≠ d := fun h => hab.2.1 (congrArg Key.name h)
    apply ih (z := z) (t := t) ?_ hab.2.2
    rw [Finmap.lookup_insert_of_ne _ hze, Finmap.lookup_erase_ne hzd]
    exact hz
  | @inpEndpoint n Γ Δ e c r k v s p hg hd hc hh ha hp ih =>
    have hze : z ≠ e := fun h => hab.1 (congrArg Key.name h)
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab.2
    rw [Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z r)]
    apply Context.lookup_lift.mpr
    rw [Finmap.lookup_insert_of_ne _ hze]
    exact hz
  | invoke hs hd hv hr he hg hb hp ih =>
    apply ih (z := z) (t := t) ?_ hab.2.2
    rw [Finmap.lookup_erase_ne (fun h => hab.2.1 (congrArg Key.name h))]
    exact hz
  | accept hs hc hscope hd hp ih => exact hc z t hz
  | serve ht hp hc hscope hd ih => exact hc z t hz
  | @par n Γ Δ Θ p q hd hp hq ihp ihq =>
    by_cases hm : z ∈ Δ
    · rw [Finmap.lookup_union_left hm] at hz
      exact ihp hz hab.1
    · rw [Finmap.lookup_union_right hm] at hz
      exact ihq hz hab.2
  | @nu n Γ Δ c p hd hp ih =>
    apply ih (z := Key.mapName (liftName 0) z) (t := t) ?_ hab
    rw [Context.bind,
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .negative),
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .positive)]
    exact Context.lookup_lift.mpr hz

/-- ALL10 runtime rules support erasure only under real all-position absence.
Accept/serve ambient erasure does NOT alter their exact fresh/empty BODY domains. -/
theorem HasType.erase_nameAbsent {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) {z : Key} (hab : NameAbsent z.name p) :
    HasType n Γ (Δ.erase z) p := by
  induction h generalizing z with
  | nil hc hs hd =>
    exact HasType.nil hc.erase (fun e he => hs e (Finmap.mem_erase.mp he).2) (hd.erase z)
  | @outName n Γ Δ e c b s p hg hd hc hh ha hb hp ih =>
    have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
    apply HasType.outName (e := e) (c := c) (s := s) hg.erase (hd.erase z)
    · rw [Finmap.lookup_erase_ne hez]; exact hc
    · exact hh
    · exact ha
    · exact hb
    · have ht := ih hab.2.2
      rw [Context.erase_insert_ne hez] at ht
      exact ht
  | @inpName n Γ Δ e c s p hg hd hc hh ha hp ih =>
    by_cases hm : z ∈ Δ
    · have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
      apply HasType.inpName (e := e) (c := c) (s := s) hg.erase (hd.erase z)
      · rw [Finmap.lookup_erase_ne hez]; exact hc
      · exact hh
      · exact ha
      · have ht := ih (z := Key.mapName (liftName 0) z) hab.2
        rw [← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
          Context.erase_insert_ne hez] at ht
        exact ht
    · rw [Context.erase_of_notMem hm]
      exact HasType.inpName hg hd hc hh ha hp
  | @outEndpoint n Γ Δ e d c v k t s p hg hd hc hh hv he hne ha hb hp ih =>
    have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
    have hdz : d ≠ z := fun he => hab.2.1 (congrArg Key.name he.symm)
    apply HasType.outEndpoint (e := e) (d := d) (c := c) (s := s) hg.erase (hd.erase z)
    · rw [Finmap.lookup_erase_ne hez]; exact hc
    · exact hh
    · rw [Finmap.lookup_erase_ne hdz]; exact hv
    · exact he
    · exact hne
    · exact ha
    · exact hb
    · have ht := ih hab.2.2
      rw [Context.erase_insert_ne hez, Finmap.erase_erase] at ht
      exact ht
  | @inpEndpoint n Γ Δ e c r k t s p hg hd hc hh ha hp ih =>
    by_cases hm : z ∈ Δ
    · have hez : e ≠ z := fun he => hab.1 (congrArg Key.name he.symm)
      apply HasType.inpEndpoint (e := e) (c := c) (r := r) (k := k) (t := t) (s := s)
        hg.erase (hd.erase z)
      · rw [Finmap.lookup_erase_ne hez]; exact hc
      · exact hh
      · exact ha
      · have ht := ih (z := Key.mapName (liftName 0) z) hab.2
        rw [Context.erase_insert_ne (Key.lift_ne_bound z r).symm,
          ← Context.lift_erase 0 (Finmap.mem_insert.mpr (Or.inr hm)),
          Context.erase_insert_ne hez] at ht
        exact ht
    · rw [Context.erase_of_notMem hm]
      exact HasType.inpEndpoint hg hd hc hh ha hp
  | @invoke n Γ Δ s sig e v p hs hd hv hr he hg hb hp ih =>
    have hez : e ≠ z := fun he => hab.2.1 (congrArg Key.name he.symm)
    apply HasType.invoke hs (hd.erase z)
    · rw [Finmap.lookup_erase_ne hez]; exact hv
    · exact hr
    · exact he
    · exact hg.erase z
    · exact hb
    · have ht := ih hab.2.2
      rw [Finmap.erase_erase] at ht
      exact ht
  | accept hs hc hscope hd hp ih =>
    exact HasType.accept hs hc.erase
      (fun e he => hscope e (Finmap.mem_erase.mp he).2) (hd.erase z) hp
  | serve ht hp hc hscope hd ih =>
    exact HasType.serve ht hp hc.erase
      (fun e he => hscope e (Finmap.mem_erase.mp he).2) (hd.erase z)
  | par hd hp hq ihp ihq =>
    rw [Context.erase_union]
    exact HasType.par
      (fun e he ht => hd e (Finmap.mem_erase.mp he).2 (Finmap.mem_erase.mp ht).2)
      (ihp hab.1) (ihq hab.2)
  | @nu n Γ Δ c p hd hp ih =>
    by_cases hm : z ∈ Δ
    · have ht := ih (z := Key.mapName (liftName 0) z) hab
      rw [Context.bind_erase c hm] at ht
      exact HasType.nu (hd.erase z) ht
    · rw [Context.erase_of_notMem hm]
      exact HasType.nu hd hp

end Cslib.SessionTypes.Endpoint.Runtime
