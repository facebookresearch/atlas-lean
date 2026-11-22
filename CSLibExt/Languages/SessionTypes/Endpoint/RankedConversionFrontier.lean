/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionReduction
public import CSLibExt.Languages.SessionTypes.Endpoint.FrontierMinimum

/-!
# Actual minimum-active guards for conversion-ranked finite frontiers

Only existing syntax normal forms and pure minimum/map/activity facts are
shared. Typing-dependent exposure and peer separation are reconstructed.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- Literal output is active and checks every other owned active key. -/
theorem RankedType.out_active {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ GuardMin Δ e c.rank := by
  cases h with
  | outName hg hc hh ha hb hp => exact ⟨_, _, rfl, hc, SendsTo.active (Or.inl hh), hg⟩
  | outEndpoint hg hc hh hv he hne ha hb hp =>
    exact ⟨_, _, rfl, hc, SendsTo.active (Or.inr ⟨_, _, _, hh⟩), hg⟩

/-- Literal input is active before either payload kind is received. -/
theorem RankedType.inp_active {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ c.protocol.unfold ≠ .done ∧ GuardMin Δ e c.rank := by
  cases h with
  | inpName hg hc hh ha hp =>
    refine ⟨_, _, rfl, hc, ?_, hg⟩
    rw [hh]
    intro he
    cases he
  | inpEndpoint hg hc hh ha hp =>
    refine ⟨_, _, rfl, hc, ?_, hg⟩
    rw [hh]
    intro he
    cases he

private theorem empty_ranked_nil (n : Nat) : RankedType n ∅ .nil :=
  RankedType.nil (by intro e c he; simp at he)
    (by intro e he; exact False.elim (Finmap.notMem_empty he))

/-- A minimum active role is exposed as the EXACT subject of an actual leaf.
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

/-- A frontier with no active ownership cannot contain a live prefix.
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


/-- A semantic equal-rank active peer cannot inhabit the selected minimum guard. -/
theorem minimum_peer_separate {n : Nat} {Γ : Context} {g : Proc} {e : Key} {c d : Capability}
    (ht : RankedType n Γ g) (he : Γ.lookup e = some c) (ha : c.protocol.unfold ≠ .done)
    (hmin : ∀ x v, Γ.lookup x = some v → v.protocol.unfold ≠ .done → c.rank ≤ v.rank)
    (hshape : (∃ b t, g = .out e.name b t) ∨ (∃ t, g = .inp e.name t))
    (hd : d.Equivalent c.dual) : Γ.lookup e.opposite ≠ some d := by
  intro hp
  have hg := minimum_prefix_guard ht he ha hmin hshape
  have hda : d.protocol.unfold ≠ .done := by
    intro hdone
    exact Capability.dual_active ha (hd.2.done_iff.mp hdone)
  have hlt := hg e.opposite d hp hda e.opposite_ne
  have hr : d.rank = c.rank := hd.1
  rw [hr] at hlt
  exact Nat.lt_irrefl c.rank hlt

end Cslib.SessionTypes.Endpoint.Conversion
