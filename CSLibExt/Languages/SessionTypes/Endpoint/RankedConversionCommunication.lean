/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionCong
public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticAdvance

/-!
# Ranked conversion head preservation at semantically compatible interfaces

Literal receiver codes and transferred actual capabilities are kept; the
new ranked substitution theorem transports all continuation guards.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Inversion of conversion-ranked input typing.**
Input inversion retains its actual advertised code and typed continuation. -/
theorem RankedType.inp_inv {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .recvName s ∧
          RankedType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p) ∨
       ∃ r k t s, c.protocol.unfold = .recvEndpoint r k t s ∧
          RankedType (n + 1)
            ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p) := by
  cases h with
  | inpName hg hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hh, hp⟩⟩
  | inpEndpoint hg hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, hh, hp⟩⟩

/-- **Passive head communication preserves conversion ranked typing.**
GENERAL passive communicating-head preservation at a semantically
compatible actual split, with literal receiver-tail and rank evidence. -/
theorem ranked_passive_head_preservation {n : Nat} {Γ Θ : Context} {e : Key} {c : Capability}
    {s : Protocol} {b : Name} {p q : Proc}
    (hd : Finmap.Disjoint Γ Θ) (hc : Γ.lookup e = some c)
    (hh : c.protocol.unfold = .sendName s)
    (hp : RankedType n (Γ.insert e ⟨c.rank, s⟩) p) (hq : RankedType n Θ (.inp e.name q))
    (hb : b.ClosedAt n) (hco : Compatible (Γ ∪ Θ)) :
    ∃ d u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvName u ∧ u.TreeEquiv s.dual ∧
      RankedType n (((Γ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q b)) := by
  obtain ⟨f, d, hn, ht, hcase⟩ := hq.inp_inv
  have he := disjoint_subjects_opposite hd hc ht hn.symm
  subst f
  have hdual := communicating_equivalent hd hc ht rfl hco
  obtain ⟨u, hu, hur⟩ := passive_peer_head hdual hh
  rcases hcase with ⟨v, hv, hbody⟩ | ⟨r, k, t, v, hv, hbody⟩
  · have htail : v = u := Protocol.recvName.inj (hv.symm.trans hu)
    subst v
    have hright := hbody.subst_passive hb
    have hleft := Context.disjoint_insert_owned (c := (⟨c.rank, s⟩ : Capability)) hd
      (Finmap.mem_of_lookup_eq_some hc)
    have hsplit := Context.disjoint_insert_owned (c := (⟨d.rank, u⟩ : Capability))
      (hleft.symm _ _) (Finmap.mem_of_lookup_eq_some ht)
    have hout := RankedType.par (hsplit.symm _ _) hp hright
    rw [Context.union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht)] at hout
    exact ⟨d, u, ht, hdual.1, hu, hur, hout⟩
  · rw [hu] at hv
    cases hv

/-- **Endpoint head communication preserves conversion ranked typing.**
At an initially semantically compatible disjoint split, endpoint head
communication transfers EXACT v, retaining the receiver's separately equivalent
advertised payload/tail codes. -/
theorem ranked_endpoint_head_preservation {n k : Nat} {Γ Θ : Context} {e f : Key}
    {c v : Capability} {t s : Protocol} {p q : Proc}
    (hd : Finmap.Disjoint Γ Θ) (hc : Γ.lookup e = some c)
    (hh : c.protocol.unfold = .sendEndpoint f.role k t s)
    (hv : Γ.lookup f = some v) (hvt : v.Equivalent ⟨k, t⟩) (hne : e ≠ f)
    (hp : RankedType n ((Γ.erase f).insert e ⟨c.rank, s⟩) p)
    (hq : RankedType n Θ (.inp e.name q)) (hb : f.name.ClosedAt n)
    (hco : Compatible (Γ ∪ Θ)) :
    ∃ d t' u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvEndpoint f.role k t' u ∧ t'.TreeEquiv t ∧ u.TreeEquiv s.dual ∧
      RankedType n (((Γ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q f.name)) := by
  obtain ⟨a, d, hn, ht, hcase⟩ := hq.inp_inv
  have he := disjoint_subjects_opposite hd hc ht hn.symm
  subst a
  have hdual := communicating_equivalent hd hc ht rfl hco
  obtain ⟨t', u, hu, htp, hus⟩ := endpoint_peer_head hdual hh
  rcases hcase with ⟨w, hw, hbody⟩ | ⟨r, l, w, z, hw, hbody⟩
  · rw [hu] at hw
    cases hw
  · obtain ⟨hr, hk, hwp, hz⟩ := Protocol.recvEndpoint.inj (hw.symm.trans hu)
    subst r
    subst l
    subst w
    subst z
    have hpayload : v.Equivalent ⟨k, t'⟩ := hvt.trans ⟨rfl, htp.symm⟩
    have hright := hbody.subst_endpoint_from_split hd hv ht hpayload hb
    have hsplit := Context.disjoint_transfer (c := (⟨c.rank, s⟩ : Capability))
      (t := (⟨d.rank, u⟩ : Capability)) (u := v) hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hne
    have hout := RankedType.par hsplit hp hright
    rw [Context.transfer_union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hv hne] at hout
    exact ⟨d, t', u, ht, hdual.1, hu, htp, hus, hout⟩

private theorem out_full_inv {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ b.ClosedAt n ∧
      ((∃ s, c.protocol.unfold = .sendName s ∧ RankedType n (Δ.insert e ⟨c.rank, s⟩) p) ∨
       ∃ f v k t s, f.name = b ∧ c.protocol.unfold = .sendEndpoint f.role k t s ∧
         Δ.lookup f = some v ∧ v.Equivalent ⟨k, t⟩ ∧ e ≠ f ∧
         RankedType n ((Δ.erase f).insert e ⟨c.rank, s⟩) p) := by
  cases h with
  | outName hg hc hh ha hb hp => exact ⟨_, _, rfl, hc, hb, Or.inl ⟨_, hh, hp⟩⟩
  | outEndpoint hg hc hh hv he hne ha hb hp =>
    exact ⟨_, _, rfl, hc, hb, Or.inr ⟨_, _, _, _, _, rfl, hh, hv, he, hne, hp⟩⟩

/-- **Head preservation for a conversion-ranked opposite pair.**
A typed opposite-head pair at an initially semantically compatible interface
yields packed literal-head preservation. Both actual heads and payload/tail
correspondence are conclusions, not fields in a protocol or admission predicate. -/
theorem RankedType.head_preservation {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : RankedType n Δ (.par (.out a b p) (.inp a q))) (hco : Compatible Δ) :
    ∃ e c d s u, e.name = a ∧ Δ.lookup e = some c ∧ Δ.lookup e.opposite = some d ∧
      d.rank = c.rank ∧ u.TreeEquiv s.dual ∧
      ((c.protocol.unfold = .sendName s ∧ d.protocol.unfold = .recvName u) ∨
       ∃ f v k t t', f.name = b ∧ Δ.lookup f = some v ∧ v.Equivalent ⟨k, t⟩ ∧
         c.protocol.unfold = .sendEndpoint f.role k t s ∧
         d.protocol.unfold = .recvEndpoint f.role k t' u ∧ t'.TreeEquiv t) ∧
      RankedType n ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q b)) := by
  cases h with
  | @par n Γ Θ ho hi hd hp hq =>
    obtain ⟨e, c, hn, hc, hb, hcase⟩ := out_full_inv hp
    subst a
    have hwhole : (Γ ∪ Θ).lookup e = some c :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
    rcases hcase with ⟨s, hs, hbody⟩ | ⟨f, v, k, t, s, hbn, hs, hv, he, hne, hbody⟩
    · obtain ⟨d, u, ht, hr, hu, heq, hout⟩ :=
        ranked_passive_head_preservation hd hc hs hbody hq hb hco
      have hpeer : (Γ ∪ Θ).lookup e.opposite = some d :=
        (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
      exact ⟨e, c, d, s, u, rfl, hwhole, hpeer, hr, heq, Or.inl ⟨hs, hu⟩, hout⟩
    · subst b
      obtain ⟨d, t', u, ht, hr, hu, htp, heq, hout⟩ :=
        ranked_endpoint_head_preservation hd hc hs hv he hne hbody hq hb hco
      have hpeer : (Γ ∪ Θ).lookup e.opposite = some d :=
        (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
      have hvwhole : (Γ ∪ Θ).lookup f = some v :=
        (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
      exact ⟨e, c, d, s, u, rfl, hwhole, hpeer, hr, heq,
        Or.inr ⟨f, v, k, t, t', rfl, hvwhole, he, hs, hu, htp⟩, hout⟩

/-- **Conversion head communication yields a semantic advance.**
For a ranked-typed opposite-head pair at an initially semantically compatible
interface, head preservation constructs a faithful semantic advance and a
compatible ranked residual. -/
theorem RankedType.head_advance {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : RankedType n Δ (.par (.out a b p) (.inp a q))) (hc : Compatible Δ) :
    ∃ Ξ, RankedType n Ξ (.par p (PiCalculus.subst q b)) ∧ Compatible Ξ ∧ SemanticAdvance Δ Ξ := by
  obtain ⟨e, c, d, s, u, hn, hs, hp, hr, ht, hh, hout⟩ := h.head_preservation hc
  have hheads : CommunicationHeads c d s u := by
    rcases hh with ⟨hs, hp⟩ | ⟨f, v, k, t, t', hb, hv, hvt, hs, hp, heq⟩
    · exact CommunicationHeads.passive hs hp
    · exact CommunicationHeads.endpoint hs hp heq
  have ha := SemanticAdvance.matched hs hp (hc e c d hs hp) hheads ht
  exact ⟨_, hout, ha.compatible hc, ha⟩

end Cslib.SessionTypes.Endpoint.Conversion
