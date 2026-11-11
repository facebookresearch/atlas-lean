/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeNormalization
public import CSLibExt.Languages.SessionTypes.Endpoint.FrontierMinimum
public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeCommunication

/-!
# Runtime-owned minimum guards and actual idle frontiers

The runtime judgement is not erased to the finite fragment. Requests are handled
separately, so shared invocations cannot hide minimum active ownership here.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- A request-free output has an ACTUAL active linear subject and GuardMin. -/
theorem HasType.linear_out_active {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    {a b : Name} {p : Proc} (h : HasType n Γ Δ (.out a b p))
    (hf : RequestFree Γ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ GuardMin Δ e c.rank := by
  cases h with
  | outName hg hs hc hh ha hb hp => exact ⟨_, _, rfl, hc, SendsTo.active (Or.inl hh), hg⟩
  | outEndpoint hg hs hc hh hv he hne ha hb hp =>
    exact ⟨_, _, rfl, hc, SendsTo.active (Or.inr ⟨_, _, _, hh⟩), hg⟩
  | invoke hs hd hv hr he hg hb hp => exact False.elim (hf _ _ hs rfl)

/-- Linear inputs expose active subjects; once-only shared accepts have only
completed AMBIENT ownership and may wait quiescently. -/
theorem HasType.inp_active_or_completed {n : Nat} {Γ : ServiceEnv} {Δ : Context}
    {a : Name} {p : Proc} (h : HasType n Γ Δ (.inp a p)) :
    (∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧
      GuardMin Δ e c.rank) ∨ Δ.Completed := by
  cases h with
  | inpName hg hs hc hh ha hp =>
    refine Or.inl ⟨_, _, rfl, hc, ?_, hg⟩
    rw [hh]
    intro h
    cases h
  | inpEndpoint hg hs hc hh ha hp =>
    refine Or.inl ⟨_, _, rfl, hc, ?_, hg⟩
    rw [hh]
    intro h
    cases h
  | accept hs hc hscope hd hp => exact Or.inr hc

/-- With no actual requests or active owned keys, typing derives ACTUAL idle
service-template syntax, not merely an empty/completed interface. -/
theorem GuardedFrontier.completed_idle {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (hf : GuardedFrontier Γ p) (ht : HasType n Γ Δ p) (hr : RequestFree Γ p)
    (hc : Δ.Completed) : ServiceTemplate Γ p := by
  induction hf generalizing n Δ with
  | template hp => exact hp
  | out =>
    obtain ⟨e, c, hn, he, ha, hg⟩ := ht.linear_out_active hr
    exact False.elim (ha (hc e c he))
  | inp =>
    cases ht with
    | inpName hg hs he hh ha hp =>
      have hd := hc _ _ he
      rw [hh] at hd
      cases hd
    | inpEndpoint hg hs he hh ha hp =>
      have hd := hc _ _ he
      rw [hh] at hd
      cases hd
    | accept hs hcomplete hscope hd hp => exact ⟨_, rfl, Finmap.mem_of_lookup_eq_some hs⟩
  | par hp hq ihp ihq =>
    obtain ⟨A, B, rfl, hd, htp, htq⟩ := ht.par_inv
    have ha : A.Completed := fun e c he =>
      hc e c ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some he)).trans he)
    have hb : B.Completed := fun e c he =>
      hc e c
        ((Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some he))).trans he)
    exact ⟨ihp htp hr.1 ha, ihq htq hr.2 hb⟩

private theorem empty_runtime_nil (n : Nat) (Γ : ServiceEnv) : HasType n Γ ∅ .nil :=
  HasType.nil Context.completed_empty (fun _ he => False.elim (Finmap.notMem_empty he))
    (separated_empty Γ)

/-- A minimum over ALL actual active owned keys exposes the EXACT linear subject
of a real runtime leaf. Idle templates/accept ambient are completed; shared outputs
are excluded only by the internally established request-free case. -/
theorem GuardedFrontier.expose_minimum {n : Nat} {Γ : ServiceEnv} {Δ : Context} {p : Proc}
    (hf : GuardedFrontier Γ p) (ht : HasType n Γ Δ p) (hr : RequestFree Γ p)
    {e : Key} {c : Capability} (he : Δ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank) :
    ∃ Λ Θ g r, Δ = Λ ∪ Θ ∧ Finmap.Disjoint Λ Θ ∧ Λ.lookup e = some c ∧
      Cong p (.par g r) ∧ HasType n Γ Λ g ∧ HasType n Γ Θ r ∧
      ((∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t)) ∧ GuardedFrontier Γ r := by
  induction hf generalizing n Δ with
  | template hp => exact False.elim (ha (ht.template_completed hp e c he))
  | out a b t =>
    obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.linear_out_active hr
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    refine ⟨Δ, ∅, .out a b t, .nil, (Finmap.union_empty).symm,
      (Finmap.disjoint_empty Δ).symm _ _, he, (Cong.par_nil _).symm, ht,
      empty_runtime_nil n Γ, Or.inl ⟨b, t, ?_⟩, .template trivial⟩
    rw [hn]
  | inp a t =>
    rcases ht.inp_active_or_completed with ⟨d, u, hn, hd, hu, hg⟩ | hc
    · have hed := minimum_guard_key he ha hd hu hg hmin
      subst d
      refine ⟨Δ, ∅, .inp a t, .nil, (Finmap.union_empty).symm,
        (Finmap.disjoint_empty Δ).symm _ _, he, (Cong.par_nil _).symm, ht,
        empty_runtime_nil n Γ, Or.inr ⟨t, ?_⟩, .template trivial⟩
      rw [hn]
    · exact False.elim (ha (hc e c he))
  | @par p q hfp hfq ihp ihq =>
    obtain ⟨A, B, rfl, hd, hp, hq⟩ := ht.par_inv
    by_cases hem : e ∈ A
    · have heA : A.lookup e = some c := by
        rw [Finmap.lookup_union_left hem] at he
        exact he
      have hminA : ∀ x v, A.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank :=
        fun x v hx hv => hmin x v
          ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)).trans hx) hv
      obtain ⟨Λ, Θ, g, r, rfl, hdis, hguard, hc, hg, hrest, hshape, hfr⟩ :=
        ihp hp hr.1 heA hminA
      obtain ⟨hΛB, hΘB⟩ := (Finmap.disjoint_union_left Λ Θ B).mp hd
      exact ⟨Λ, Θ ∪ B, g, .par r q, Finmap.union_assoc,
        (Finmap.disjoint_union_right Λ Θ B).mpr ⟨hdis, hΛB⟩, hguard,
        Cong.trans (Cong.par_cong hc (Cong.refl q)) (Cong.par_assoc g r q), hg,
        HasType.par hΘB hrest hq, hshape, .par hfr hfq⟩
    · have heB : B.lookup e = some c := by
        rw [Finmap.lookup_union_right hem] at he
        exact he
      have hminB : ∀ x v, B.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
        intro x v hx hv
        exact hmin x v ((Finmap.lookup_union_right
          (hd.symm _ _ x (Finmap.mem_of_lookup_eq_some hx))).trans hx) hv
      obtain ⟨Λ, Θ, g, r, rfl, hdis, hguard, hc, hg, hrest, hshape, hfr⟩ :=
        ihq hq hr.2 heB hminB
      obtain ⟨hAΛ, hAΘ⟩ := (Finmap.disjoint_union_right A Λ Θ).mp hd
      refine ⟨Λ, Θ ∪ A, g, .par r p, ?_,
        (Finmap.disjoint_union_right Λ Θ A).mpr ⟨hdis, hAΛ.symm _ _⟩, hguard,
        Cong.trans (Cong.par_cong (Cong.refl p) hc)
          (Cong.trans (Cong.par_comm p (.par g r)) (Cong.par_assoc g r p)), hg,
        HasType.par (hAΘ.symm _ _) hrest hp, hshape, .par hfr hfp⟩
      rw [Finmap.union_comm_of_disjoint hd, Finmap.union_assoc]

private theorem minimum_prefix_guard {n : Nat} {Γ : ServiceEnv} {Δ : Context} {g : Proc}
    {e : Key} {c : Capability} (ht : HasType n Γ Δ g) (hr : RequestFree Γ g)
    (he : Δ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank)
    (hs : (∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t)) :
    GuardMin Δ e c.rank := by
  rcases hs with ⟨b, t, rfl⟩ | ⟨t, rfl⟩
  · obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.linear_out_active hr
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    have hcu := Context.unique hd he
    subst u
    exact hg
  · rcases ht.inp_active_or_completed with ⟨d, u, hn, hd, hu, hg⟩ | hc
    · have hed := minimum_guard_key he ha hd hu hg hmin
      subst d
      have hcu := Context.unique hd he
      subst u
      exact hg
    · exact False.elim (ha (hc e c he))

/-- The equal-rank semantic peer of a minimum active role cannot share its
actual guard leaf. Opposite roles on the SAME physical name are distinct keys. -/
theorem minimum_peer_separate {n : Nat} {Γ : ServiceEnv} {Δ : Context} {g : Proc}
    {e : Key} {c d : Capability} (ht : HasType n Γ Δ g) (hr : RequestFree Γ g)
    (he : Δ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank)
    (hs : (∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t))
    (hd : d.Equivalent c.dual) : Δ.lookup e.opposite ≠ some d := by
  intro hp
  have hg := minimum_prefix_guard ht hr he ha hmin hs
  have hda : d.protocol.unfold ≠ .done := by
    intro hdone
    exact Capability.dual_active ha (hd.2.done_iff.mp hdone)
  have hlt := hg e.opposite d hp hda e.opposite_ne
  rw [hd.1] at hlt
  exact Nat.lt_irrefl c.rank hlt

end Cslib.SessionTypes.Endpoint.Runtime
