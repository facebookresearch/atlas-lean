/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeAbsence

/-!
# Runtime context scope and completed guarded-template annotations
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Each owned key of a runtime typing is scoped at ambient depth.**
Every actual owned key is scoped at the runtime derivation's ambient depth. -/
theorem HasType.lookup_closedAt {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) {z : Key} {t : Capability} (hz : Δ.lookup z = some t) :
    z.name.ClosedAt n := by
  induction h generalizing z t with
  | nil hc hs hd => exact hs z (Finmap.mem_of_lookup_eq_some hz)
  | @outName n Γ Δ e c b s p hg hd hc hh ha hb hp ih =>
    by_cases he : z = e
    · exact he ▸ ha
    · apply ih (z := z) (t := t)
      rw [Finmap.lookup_insert_of_ne _ he]
      exact hz
  | @inpName n Γ Δ e c s p hg hd hc hh ha hp ih =>
    by_cases he : z = e
    · exact he ▸ ha
    · apply (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mp
      apply ih (z := Key.mapName (liftName 0) z) (t := t)
      apply Context.lookup_lift.mpr
      rw [Finmap.lookup_insert_of_ne _ he]
      exact hz
  | @outEndpoint n Γ Δ e d c v k advertised s p hg hd hc hh hv he hne ha hb hp ih =>
    by_cases hze : z = e
    · exact hze ▸ ha
    · by_cases hzd : z = d
      · exact hzd ▸ hb
      · apply ih (z := z) (t := t)
        rw [Finmap.lookup_insert_of_ne _ hze, Finmap.lookup_erase_ne hzd]
        exact hz
  | @inpEndpoint n Γ Δ e c r k advertised s p hg hd hc hh ha hp ih =>
    by_cases he : z = e
    · exact he ▸ ha
    · apply (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mp
      apply ih (z := Key.mapName (liftName 0) z) (t := t)
      rw [Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z r)]
      apply Context.lookup_lift.mpr
      rw [Finmap.lookup_insert_of_ne _ he]
      exact hz
  | @invoke n Γ Δ s sig e v p hs hd hv hr he hg hb hp ih =>
    by_cases hze : z = e
    · exact hze ▸ hb
    · apply ih (z := z) (t := t)
      rw [Finmap.lookup_erase_ne hze]
      exact hz
  | accept hs hc hscope hd hp ih => exact hscope z (Finmap.mem_of_lookup_eq_some hz)
  | serve ht hp hc hscope hd ih => exact hscope z (Finmap.mem_of_lookup_eq_some hz)
  | @par n Γ Δ Θ p q hd hp hq ihp ihq =>
    by_cases hm : z ∈ Δ
    · rw [Finmap.lookup_union_left hm] at hz
      exact ihp hz
    · rw [Finmap.lookup_union_right hm] at hz
      exact ihq hz
  | @nu n Γ Δ c p hd hp ih =>
    apply (closedAt_liftName_iff _ 0 (Nat.zero_le _) z.name).mp
    apply ih (z := Key.mapName (liftName 0) z) (t := t)
    rw [Context.bind,
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .negative),
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound z .positive)]
    exact Context.lookup_lift.mpr hz

/-- **Whole owned context of a runtime typing is scoped at ambient depth.**
Scope applies to the actual complete owned domain, not only active subjects. -/
theorem HasType.context_closedAt {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) : ∀ e ∈ Δ, e.name.ClosedAt n := by
  intro e he
  obtain ⟨c, hc⟩ := Finmap.mem_iff.mp he
  exact h.lookup_closedAt hc

/-- **Typed service templates own only completed entries.**
A typed structurally guarded template owns only completed AMBIENT entries.
Its input and replica BODY proofs remain separate and may use their own formal key. -/
theorem HasType.template_completed {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (ht : ServiceTemplate Γ p) : Δ.Completed := by
  induction h with
  | nil hc hs hd => exact hc
  | outName => exact False.elim ht
  | @inpName n Γ Δ e c s p hg hd hc hh ha hp ih =>
    obtain ⟨s, hs, hm⟩ := ht
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hm
    exact False.elim (hd e c hc s sig hsig hs)
  | outEndpoint => exact False.elim ht
  | @inpEndpoint n Γ Δ e c r k t s p hg hd hc hh ha hp ih =>
    obtain ⟨s, hs, hm⟩ := ht
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hm
    exact False.elim (hd e c hc s sig hsig hs)
  | invoke => exact False.elim ht
  | accept hs hc hscope hd hp ih => exact hc
  | serve ht hp hc hscope hd ih => exact hc
  | @par n Γ Δ Θ p q hd hp hq ihp ihq =>
    intro e c hc
    by_cases hm : e ∈ Δ
    · rw [Finmap.lookup_union_left hm] at hc
      exact ihp ht.1 e c hc
    · rw [Finmap.lookup_union_right hm] at hc
      exact ihq ht.2 e c hc
  | @nu n Γ Δ c p hd hp ih =>
    intro e t he
    apply ih ht (Key.mapName (liftName 0) e) t
    rw [Context.bind,
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound e .negative),
      Finmap.lookup_insert_of_ne _ (Key.lift_ne_bound e .positive)]
    exact Context.lookup_lift.mpr he

private theorem completed_bind {Δ : Context} {c : Capability}
    (hc : Δ.Completed) (hd : c.protocol.unfold = .done) : (Context.bind c Δ).Completed := by
  have hl : (Context.lift 0 Δ).Completed := hc.rekey _
  have hd' : c.dual.protocol.unfold = .done := by
    simp only [Capability.dual, Protocol.unfold_dual, hd, Protocol.dual]
  exact (hl.insert hd).insert hd'

private theorem scope_bind {n : Nat} {Δ : Context} (c : Capability)
    (hs : ∀ e ∈ Δ, e.name.ClosedAt n) :
    ∀ e ∈ Context.bind c Δ, e.name.ClosedAt (n + 1) := by
  intro e he
  rcases Finmap.mem_insert.mp he with rfl | he
  · exact Nat.zero_lt_succ n
  · rcases Finmap.mem_insert.mp he with rfl | he
    · exact Nat.zero_lt_succ n
    · obtain ⟨d, hd, rfl⟩ := Context.mem_rekey.mp he
      exact (closedAt_liftName_iff _ 0 (Nat.zero_le _) d.name).mpr (hs d hd)

/-- **Typed service templates retype at any well-formed completed context.**
Structurally guarded typed templates can replace only their COMPLETED ambient
annotations. Fresh input/empty replica BODY proofs are retained unchanged. -/
theorem HasType.template_reannotate {n : Nat} {Γ : ServiceEnv} {Δ Θ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (ht : ServiceTemplate Γ p) (hc : Θ.Completed)
    (hs : ∀ e ∈ Θ, e.name.ClosedAt n) (hd : Separated Γ Θ) : HasType n Γ Θ p := by
  induction h generalizing Θ with
  | nil => exact HasType.nil hc hs hd
  | outName => exact False.elim ht
  | @inpName n Γ Δ e c s p hg hsep hlook hh ha hp ih =>
    obtain ⟨s, hn, hm⟩ := ht
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hm
    exact False.elim (hsep e c hlook s sig hsig hn)
  | outEndpoint => exact False.elim ht
  | @inpEndpoint n Γ Δ e c r k t s p hg hsep hlook hh ha hp ih =>
    obtain ⟨s, hn, hm⟩ := ht
    obtain ⟨sig, hsig⟩ := Finmap.mem_iff.mp hm
    exact False.elim (hsep e c hlook s sig hsig hn)
  | invoke => exact False.elim ht
  | accept hsig hcomplete hscope hsep hp ih => exact HasType.accept hsig hc hs hd hp
  | serve htemplate hp hcomplete hscope hsep ih => exact HasType.serve htemplate hp hc hs hd
  | @par n Γ Δ Ξ p q hdis hp hq ihp ihq =>
    have hleft := ihp ht.1 hc hs hd
    have hright := ihq ht.2 Context.completed_empty
      (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty Γ)
    have hpar := HasType.par (fun _ _ he => Finmap.notMem_empty he) hleft hright
    simpa only [Finmap.union_empty] using hpar
  | @nu n Γ Δ c p hsep hp ih =>
    have hdone := hp.template_completed ht ⟨.var 0, .positive⟩ c
      (Context.lookup_bind_positive c Δ)
    exact HasType.nu hd (ih ht (completed_bind hc hdone) (scope_bind c hs) (hd.bind c))

/-- **Typed service templates retype at empty ownership.**
Clearing completed template annotations produces the EXACT empty BODY
required by replica admission; this is not unconditional active-resource erasure. -/
theorem HasType.template_empty {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (h : HasType n Γ Δ p) (ht : ServiceTemplate Γ p) : HasType n Γ ∅ p :=
  h.template_reannotate ht Context.completed_empty
    (fun _ he => False.elim (Finmap.notMem_empty he)) (separated_empty Γ)

/-- **Removing a restriction around nil preserves runtime typing.**
Removing a nil restriction retains its actual completed/scoped/separated ambient. -/
theorem HasType.nu_nil_elim {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    (h : HasType n Γ Δ (.nu .nil)) : HasType n Γ Δ .nil :=
  HasType.nil (h.template_completed trivial) h.context_closedAt h.separated

/-- **Adding a restriction around nil preserves runtime typing.**
Introducing a nil restriction chooses a genuinely completed literal-dual pair. -/
theorem HasType.nu_nil_intro {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    (h : HasType n Γ Δ .nil) : HasType n Γ Δ (.nu .nil) := by
  let c : Capability := ⟨0, .done⟩
  exact HasType.nu (c := c) h.separated
    (HasType.nil (completed_bind h.nil_inv.1 rfl) (scope_bind c h.nil_inv.2.1)
      (h.separated.bind c))

end Cslib.SessionTypes.Endpoint.Runtime
