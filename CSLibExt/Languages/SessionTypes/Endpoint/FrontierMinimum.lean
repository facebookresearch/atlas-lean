/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.FrontierNormalization
public import CSLibExt.Languages.SessionTypes.Endpoint.RankedCommunication

/-!
# Minimum active ownership in a ranked guard frontier

Minimum ranks and extracted guards are conclusions derived from finite
ownership and syntax. They are not caller readiness or progress assumptions.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Send heads are active for both payload sorts.**
Every literal communication head is active, for both payload sorts. -/
theorem SendsTo.active {c : Capability} {s : Protocol} (h : SendsTo c s) :
    c.protocol.unfold ≠ .done := by
  rcases h with h | ⟨r, k, v, h⟩ <;> rw [h] <;> intro he <;> cases he

/-- **A minimum active role owned by a guard is its subject key.**
A minimum active role owned by a prefix must be that prefix's exact
subject key, not merely a same-name role. Every other key ranks later. -/
theorem minimum_guard_key {Δ : Context} {e d : Key} {c u : Capability}
    (he : Δ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hd : Δ.lookup d = some u) (hu : u.protocol.unfold ≠ .done)
    (hg : GuardMin Δ d u.rank)
    (hmin : ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank) :
    e = d := by
  by_contra hne
  have hlt := hg e c he ha hne
  have hle := hmin d u hd hu
  omega

/-- **Ranked output subjects are active.**
Literal output subjects have an active protocol, without any stored
reduction or exposed-ready-pair evidence. -/
theorem RankedType.out_active {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ GuardMin Δ e c.rank := by
  obtain ⟨e, c, hn, hc, hg, hs⟩ := h.out_inv
  rcases hs with ⟨s, hs, hp⟩ | ⟨d, k, v, s, hn', hs, hd, he, hp⟩
  · exact ⟨e, c, hn, hc, (SendsTo.active (Or.inl hs)), hg⟩
  · exact ⟨e, c, hn, hc, (SendsTo.active (Or.inr ⟨_, _, _, hs⟩)), hg⟩

/-- **Ranked input subjects are active.**
Literal input subjects likewise own active receive heads. -/
theorem RankedType.inp_active {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ GuardMin Δ e c.rank := by
  obtain ⟨e, c, hn, hc, hg, hs⟩ := h.inp_inv
  rcases hs with ⟨s, hs, hp⟩ | ⟨r, k, v, s, hs, hp⟩
  · refine ⟨e, c, hn, hc, ?_, hg⟩
    rw [hs]
    intro he
    cases he
  · refine ⟨e, c, hn, hc, ?_, hg⟩
    rw [hs]
    intro he
    cases he

private theorem empty_ranked_nil (n : Nat) : RankedType n ∅ .nil :=
  RankedType.nil (by intro e c he; simp at he)
    (by intro e he; exact False.elim (Finmap.notMem_empty he))

/-- **Minimum active role is the subject of a frontier leaf.**
A minimum active role is exposed as the EXACT subject of an actual leaf.
The disjoint ownership split and canonical rearrangement are DERIVED outputs;
no ready guard or normalizing typing result is required from the caller. -/
theorem GuardFrontier.expose_minimum {n : Nat} {Δ : Context} {p : Proc}
    (hf : GuardFrontier p) (ht : RankedType n Δ p) {e : Key} {c : Capability}
    (he : Δ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank) :
    ∃ Γ Θ g r, Δ = Γ ∪ Θ ∧ Finmap.Disjoint Γ Θ ∧ Γ.lookup e = some c ∧
      Cong p (.par g r) ∧ RankedType n Γ g ∧ RankedType n Θ r ∧
      ((∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t)) ∧ GuardFrontier r := by
  induction hf generalizing n Δ with
  | nil => exact False.elim (ha (ht.hasType.nil_inv.1 e c he))
  | out a b t =>
    obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.out_active
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    refine ⟨Δ, ∅, .out a b t, .nil, (Finmap.union_empty).symm,
      (Finmap.disjoint_empty Δ).symm _ _, he, Cong.symm (Cong.par_nil _), ht,
      empty_ranked_nil n, ⟨Or.inl ⟨b, t, ?_⟩, GuardFrontier.nil⟩⟩
    rw [hn]
  | inp a t =>
    obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.inp_active
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    refine ⟨Δ, ∅, .inp a t, .nil, (Finmap.union_empty).symm,
      (Finmap.disjoint_empty Δ).symm _ _, he, Cong.symm (Cong.par_nil _), ht,
      empty_ranked_nil n, ⟨Or.inr ⟨t, ?_⟩, GuardFrontier.nil⟩⟩
    rw [hn]
  | @par p q hfp hfq ihp ihq =>
    obtain ⟨A, B, rfl, hd, hp, hq⟩ := ht.par_inv
    by_cases hem : e ∈ A
    · have heA : A.lookup e = some c := by
        rw [Finmap.lookup_union_left hem] at he
        exact he
      have hminA : ∀ x v, A.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
        intro x v hx hv
        exact hmin x v ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)).trans hx) hv
      obtain ⟨Γ, Θ, g, r, rfl, hdis, hguard, hc, hg, hr, ⟨hshape, hfr⟩⟩ := ihp hp heA hminA
      obtain ⟨hΓB, hΘB⟩ := (Finmap.disjoint_union_left Γ Θ B).mp hd
      refine ⟨Γ, Θ ∪ B, g, .par r q, Finmap.union_assoc,
        (Finmap.disjoint_union_right Γ Θ B).mpr ⟨hdis, hΓB⟩, hguard,
        Cong.trans (Cong.par_cong hc (Cong.refl q)) (Cong.par_assoc g r q), hg,
        RankedType.par hΘB hr hq, ⟨hshape, GuardFrontier.par hfr hfq⟩⟩
    · have heB : B.lookup e = some c := by
        rw [Finmap.lookup_union_right hem] at he
        exact he
      have hminB : ∀ x v, B.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
        intro x v hx hv
        have hxA : x ∉ A := hd.symm _ _ x (Finmap.mem_of_lookup_eq_some hx)
        exact hmin x v ((Finmap.lookup_union_right hxA).trans hx) hv
      obtain ⟨Γ, Θ, g, r, rfl, hdis, hguard, hc, hg, hr, ⟨hshape, hfr⟩⟩ := ihq hq heB hminB
      obtain ⟨hAΓ, hAΘ⟩ := (Finmap.disjoint_union_right A Γ Θ).mp hd
      refine ⟨Γ, Θ ∪ A, g, .par r p, ?_,
        (Finmap.disjoint_union_right Γ Θ A).mpr ⟨hdis, hAΓ.symm _ _⟩, hguard,
        Cong.trans (Cong.par_cong (Cong.refl p) hc)
          (Cong.trans (Cong.par_comm p (.par g r)) (Cong.par_assoc g r p)), hg,
        RankedType.par (hAΘ.symm _ _) hr hp, ⟨hshape, GuardFrontier.par hfr hfp⟩⟩
      rw [Finmap.union_comm_of_disjoint hd, Finmap.union_assoc]

/-- **Existence of a least-rank active binding.**
A nonempty collection of active finite-map bindings has a least rank.
The witness ranges over ALL active roles, not only input guards. -/
theorem Context.active_minimum {Δ : Context}
    (hactive : ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done) :
    ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧
      ∀ x v, Δ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank := by
  classical
  have hex : ∃ k : Nat, ∃ e c, Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ c.rank = k := by
    obtain ⟨e, c, hc, ha⟩ := hactive
    exact ⟨c.rank, e, c, hc, ha, rfl⟩
  obtain ⟨e, c, hc, ha, hr⟩ := Nat.find_spec hex
  refine ⟨e, c, hc, ha, ?_⟩
  intro x v hx hv
  rw [hr]
  exact Nat.find_min' hex ⟨x, v, hx, hv, rfl⟩

/-- **Completed ranked frontiers are congruent to nil.**
A frontier with no active ownership cannot contain a live prefix.
Completion is the PROCESS congruence to nil, not a completed empty interface. -/
theorem GuardFrontier.completed_nil {n : Nat} {Δ : Context} {p : Proc}
    (hf : GuardFrontier p) (ht : RankedType n Δ p) (hc : Δ.Completed) : Cong p .nil := by
  induction hf generalizing n Δ with
  | nil => exact Cong.refl _
  | out =>
    obtain ⟨e, c, hn, he, ha, hg⟩ := ht.out_active
    exact False.elim (ha (hc e c he))
  | inp =>
    obtain ⟨e, c, hn, he, ha, hg⟩ := ht.inp_active
    exact False.elim (ha (hc e c he))
  | par hp hq ihp ihq =>
    obtain ⟨Γ, Ξ, rfl, hd, htp, htq⟩ := ht.par_inv
    have hΓ : Γ.Completed := by
      intro e c he
      exact hc e c ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some he)).trans he)
    have hΞ : Ξ.Completed := by
      intro e c he
      have hn : e ∉ Γ := hd.symm _ _ e (Finmap.mem_of_lookup_eq_some he)
      exact hc e c ((Finmap.lookup_union_right hn).trans he)
    exact Cong.trans (Cong.par_cong (ihp htp hΓ) (ihq htq hΞ)) (Cong.par_nil .nil)

/-- **Duality preserves activity of a capability.**
Activity is preserved by protocol duality, including regular unfolding. -/
theorem Capability.dual_active {c : Capability} (h : c.protocol.unfold ≠ .done) :
    c.dual.protocol.unfold ≠ .done := by
  intro he
  have hd := congrArg Protocol.dual he
  change c.protocol.dual.unfold.dual = Protocol.done.dual at hd
  rw [Protocol.unfold_dual, Protocol.dual_dual] at hd
  exact h hd

private theorem minimum_prefix_guard {n : Nat} {Γ : Context} {g : Proc}
    {e : Key} {c : Capability} (ht : RankedType n Γ g)
    (he : Γ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Γ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank)
    (hshape : (∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t)) :
    GuardMin Γ e c.rank := by
  rcases hshape with ⟨b, t, rfl⟩ | ⟨t, rfl⟩
  · obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.out_active
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    have hcu := Context.unique hd he
    subst u
    exact hg
  · obtain ⟨d, u, hn, hd, hu, hg⟩ := ht.inp_active
    have hed := minimum_guard_key he ha hd hu hg hmin
    subst d
    have hcu := Context.unique hd he
    subst u
    exact hg

/-- **Minimum guard leaf cannot own its dual peer.**
A minimum active role's peer cannot be owned by the same guard leaf.
Equal-rank opposite keys violate the actual pre-action GuardMin constraint. -/
theorem minimum_peer_separate {n : Nat} {Γ : Context} {g : Proc} {e : Key} {c : Capability}
    (ht : RankedType n Γ g) (he : Γ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Γ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank)
    (hshape : (∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t)) :
    Γ.lookup e.opposite ≠ some c.dual := by
  intro hp
  have hg := minimum_prefix_guard ht he ha hmin hshape
  have hlt := hg e.opposite c.dual hp (Capability.dual_active ha) e.opposite_ne
  exact Nat.lt_irrefl c.rank hlt

end Cslib.SessionTypes.Endpoint
