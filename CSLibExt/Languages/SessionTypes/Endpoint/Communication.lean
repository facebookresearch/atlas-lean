/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Balance
public import CSLibExt.Languages.SessionTypes.Endpoint.Substitution

/-!
# Literal communication preservation at compatible finite polarized interfaces

The reductions use existing π Step and substitution. This module supplies
the head-communication case used by the full canonical Step preservation
proof in SubjectReduction.lean.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Communicating subjects in a compatible split have dual capabilities.**
Disjoint complementary subjects in a compatible interface have exactly
dual protocol capabilities, including their ranks and endpoint payload sorts. -/
theorem communicating_capabilities_dual {Δ Θ : Context} {e d : Key}
    {c t : Capability} (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (ht : Θ.lookup d = some t) (hn : e.name = d.name)
    (hco : Compatible (Δ ∪ Θ)) : t = c.dual := by
  have he := disjoint_subjects_opposite hd hc ht hn
  subst d
  apply hco e c t
  · exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
  · have hnot : e.opposite ∉ Δ :=
      Finmap.Disjoint.symm _ _ hd e.opposite (Finmap.mem_of_lookup_eq_some ht)
    exact (Finmap.lookup_union_right hnot).trans ht

/-- **Dual of a passive send head is a passive receive head.**
Actual endpoint protocols and rank equality force matching passive
receive guards at a complementary owned role. -/
theorem passive_dual_head {c t : Capability} {s : Protocol}
    (hd : t = c.dual) (hs : c.protocol.unfold = .sendName s) :
    t.protocol.unfold = .recvName s.dual := by
  subst t
  change c.protocol.dual.unfold = _
  rw [Protocol.unfold_dual, hs]
  rfl

/-- **Passive-payload communication preserves endpoint typing.**
At a compatible combined interface with the stated disjoint typed split
and scoped passive payload, head communication advances the two complementary
roles and no other capability in the exact residual context. -/
theorem passive_head_preservation {n : Nat} {Δ Θ : Context} {e : Key}
    {c : Capability} {s : Protocol} {b : Name} {p q : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendName s)
    (hp : HasType n (Δ.insert e ⟨c.rank, s⟩) p)
    (hq : HasType n Θ (.inp e.name q)) (hb : b.ClosedAt n)
    (hco : Compatible (Δ ∪ Θ)) :
    HasType n (((Δ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
      (.par p (PiCalculus.subst q b)) := by
  obtain ⟨d, t, hn, ht, hcase⟩ := hq.inp_inv
  have hdual := communicating_capabilities_dual hd hc ht hn.symm hco
  have heq := disjoint_subjects_opposite hd hc ht hn.symm
  subst d
  rcases hcase with ⟨u, hu, hbody⟩ | ⟨r, k, v, u, hu, hbody⟩
  · have hhead := passive_dual_head hdual hs
    have hsu : u = s.dual := Protocol.recvName.inj (hu.symm.trans hhead)
    subst u
    subst t
    have hr := hbody.subst_passive hb
    have hleft := Context.disjoint_insert_owned (c := (⟨c.rank, s⟩ : Capability))
      hd (Finmap.mem_of_lookup_eq_some hc)
    have hright := Context.disjoint_insert_owned
      (c := (⟨c.rank, s.dual⟩ : Capability)) (Finmap.Disjoint.symm _ _ hleft)
      (Finmap.mem_of_lookup_eq_some ht)
    have htyped := HasType.par (Finmap.Disjoint.symm _ _ hright) hp hr
    rw [Context.union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht)] at htyped
    exact htyped
  · have hhead := passive_dual_head hdual hs
    rw [hhead] at hu
    cases hu

/-- **Dual of an endpoint send head is an endpoint receive head.**
Duality preserves a delegated payload's role/rank/protocol while
reversing only the subject continuation. -/
theorem endpoint_dual_head {c t : Capability} {r : Role} {k : Nat}
    {v s : Protocol} (hd : t = c.dual)
    (hs : c.protocol.unfold = .sendEndpoint r k v s) :
    t.protocol.unfold = .recvEndpoint r k v s.dual := by
  subst t
  change c.protocol.dual.unfold = _
  rw [Protocol.unfold_dual, hs]
  rfl

/-- **Communicating subjects in a compatible split have equal ranks.**
For disjoint owned same-name roles in a compatible combined interface,
their capability ranks agree, as required by exact capability duality. -/
theorem communicating_ranks_equal {Δ Θ : Context} {e d : Key}
    {c t : Capability} (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (ht : Θ.lookup d = some t) (hn : e.name = d.name)
    (hco : Compatible (Δ ∪ Θ)) : t.rank = c.rank := by
  have he := communicating_capabilities_dual hd hc ht hn hco
  have hr : t.rank = c.dual.rank := congrArg Capability.rank he
  exact hr

/-- **Endpoint-delegating communication preserves typing.**
At a compatible combined interface with the stated disjoint typed split,
owned payload distinct from the carrier and scoped payload name, endpoint
communication transfers the payload role once and advances only the carrier. -/
theorem endpoint_head_preservation {n k : Nat} {Δ Θ : Context} {e d : Key}
    {c : Capability} {v s : Protocol} {p q : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendEndpoint d.role k v s)
    (hv : Δ.lookup d = some ⟨k, v⟩) (hne : e ≠ d)
    (hp : HasType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p)
    (hq : HasType n Θ (.inp e.name q)) (hb : d.name.ClosedAt n)
    (hco : Compatible (Δ ∪ Θ)) :
    HasType n (((Δ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
      (.par p (PiCalculus.subst q d.name)) := by
  obtain ⟨f, t, hn, ht, hcase⟩ := hq.inp_inv
  have hdual := communicating_capabilities_dual hd hc ht hn.symm hco
  have heq := disjoint_subjects_opposite hd hc ht hn.symm
  subst f
  rcases hcase with ⟨u, hu, hbody⟩ | ⟨r, l, w, u, hu, hbody⟩
  · have hhead := endpoint_dual_head hdual hs
    rw [hhead] at hu
    cases hu
  · have hhead := endpoint_dual_head hdual hs
    obtain ⟨hr, hl, hw, hs'⟩ := Protocol.recvEndpoint.inj (hu.symm.trans hhead)
    subst r
    subst l
    subst w
    subst u
    subst t
    have hrec := hbody.subst_endpoint_from_split hd hv ht hb
    have hsplit := Context.disjoint_transfer
      (c := (⟨c.rank, s⟩ : Capability))
      (t := (⟨c.rank, s.dual⟩ : Capability)) (u := (⟨k, v⟩ : Capability))
      hd (Finmap.mem_of_lookup_eq_some hc) (Finmap.mem_of_lookup_eq_some ht) hne
    have htyped := HasType.par hsplit hp hrec
    rw [Context.transfer_union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hv hne] at htyped
    exact htyped

/-- **Head communication preserves endpoint typing.**
For a typed opposite-head pair at an initially compatible interface,
direct communication in the existing π syntax yields an exact typed residual
ownership context, including endpoint delegation. -/
theorem HasType.head_comm_preservation {n : Nat} {Δ : Context} {a b : Name}
    {p q : Proc} (h : HasType n Δ (.par (.out a b p) (.inp a q)))
    (hco : Compatible Δ) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧
      HasType n ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
        (.par p (PiCalculus.subst q b)) := by
  obtain ⟨Θ, Ξ, rfl, hd, ho, hi⟩ := h.par_inv
  have hb : b.ClosedAt n := ho.closedAt.2.1
  obtain ⟨e, c, hn, hc, hcase⟩ := ho.out_inv
  subst a
  have hwhole : (Θ ∪ Ξ).lookup e = some c :=
    (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
  rcases hcase with ⟨s, hs, hp⟩ | ⟨d, k, v, s, hbname, hs, hv, hne, hp⟩
  · exact ⟨e, c, s, rfl, hwhole, passive_head_preservation hd hc hs hp hi hb hco⟩
  · subst b
    exact ⟨e, c, s, rfl, hwhole,
      endpoint_head_preservation hd hc hs hv hne hp hi hb hco⟩

end Cslib.SessionTypes.Endpoint
