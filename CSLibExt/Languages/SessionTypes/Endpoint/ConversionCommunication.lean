/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionSubstitution
public import CSLibExt.Languages.SessionTypes.Endpoint.Communication

/-!
# Semantically compatible literal communication heads

Receiver continuation codes are retained, not equated syntactically with the
sender's dual tail. The actual transferred capability retains its raw code.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Communicating subjects have semantically dual capabilities.**
At a semantically compatible combined interface, actual disjoint same-name
ownership derives opposite roles, literal cap-rank agreement and semantic
duality, not raw capability equality. -/
theorem communicating_equivalent {Γ Θ : Context} {e f : Key} {c d : Capability}
    (hd : Finmap.Disjoint Γ Θ) (hc : Γ.lookup e = some c) (hp : Θ.lookup f = some d)
    (hn : e.name = f.name) (hco : Compatible (Γ ∪ Θ)) : d.Equivalent c.dual := by
  have he := disjoint_subjects_opposite hd hc hp hn
  subst f
  apply hco e c d
  · exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
  · exact (Finmap.lookup_union_right
      (hd.symm _ _ e.opposite (Finmap.mem_of_lookup_eq_some hp))).trans hp

/-- **Peer of a passive send head has an equivalent receive head.**
Semantic duality forces an actual receive-name head and equivalent tail,
while keeping the receiver's literal continuation code. -/
theorem passive_peer_head {c d : Capability} {s : Protocol}
    (he : d.Equivalent c.dual) (hh : c.protocol.unfold = .sendName s) :
    ∃ u, d.protocol.unfold = .recvName u ∧ u.TreeEquiv s.dual := by
  have hm := he.2.symm.head
  change HeadMatch Protocol.TreeEquiv c.protocol.dual.unfold d.protocol.unfold at hm
  rw [Protocol.unfold_dual, hh] at hm
  generalize hu : d.protocol.unfold = t at hm
  cases hm with
  | recvName hr => exact ⟨_, rfl, hr.symm⟩

/-- **Peer of an endpoint send head has an equivalent receive head.**
Endpoint peer heads preserve literal advertised role/rank, independently
equivalent payload and continuation branches, and payload orientation. -/
theorem endpoint_peer_head {c d : Capability} {r : Role} {k : Nat} {t s : Protocol}
    (he : d.Equivalent c.dual) (hh : c.protocol.unfold = .sendEndpoint r k t s) :
    ∃ v u, d.protocol.unfold = .recvEndpoint r k v u ∧ v.TreeEquiv t ∧ u.TreeEquiv s.dual := by
  have hm := he.2.symm.head
  change HeadMatch Protocol.TreeEquiv c.protocol.dual.unfold d.protocol.unfold at hm
  rw [Protocol.unfold_dual, hh] at hm
  generalize hu : d.protocol.unfold = q at hm
  cases hm with
  | recvEndpoint hv hs => exact ⟨_, _, rfl, hv.symm, hs.symm⟩

/-- **Input inversion for conversion typing.**
Input inversion retains its actual advertised code and typed continuation. -/
theorem HasType.inp_inv {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : HasType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .recvName s ∧
          HasType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p) ∨
       ∃ r k t s, c.protocol.unfold = .recvEndpoint r k t s ∧
          HasType (n + 1)
            ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p) := by
  cases h with
  | inpName hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hh, hp⟩⟩
  | inpEndpoint hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, hh, hp⟩⟩

/-- **Passive head communication preserves conversion typing.**
GENERAL passive communicating-head preservation at a semantically
compatible actual split, with literal receiver-tail and rank evidence. -/
theorem passive_head_preservation {n : Nat} {Γ Θ : Context} {e : Key} {c : Capability}
    {s : Protocol} {b : Name} {p q : Proc}
    (hd : Finmap.Disjoint Γ Θ) (hc : Γ.lookup e = some c)
    (hh : c.protocol.unfold = .sendName s)
    (hp : HasType n (Γ.insert e ⟨c.rank, s⟩) p) (hq : HasType n Θ (.inp e.name q))
    (hb : b.ClosedAt n) (hco : Compatible (Γ ∪ Θ)) :
    ∃ d u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvName u ∧ u.TreeEquiv s.dual ∧
      HasType n (((Γ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
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
    have hout := HasType.par (hsplit.symm _ _) hp hright
    rw [Context.union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht)] at hout
    exact ⟨d, u, ht, hdual.1, hu, hur, hout⟩
  · rw [hu] at hv
    cases hv

/-- **Endpoint delegation preserves conversion typing.**
At an initially semantically compatible disjoint split, endpoint head
communication transfers EXACT v, retaining the receiver's separately equivalent
advertised payload/tail codes. -/
theorem endpoint_head_preservation {n k : Nat} {Γ Θ : Context} {e f : Key}
    {c v : Capability} {t s : Protocol} {p q : Proc}
    (hd : Finmap.Disjoint Γ Θ) (hc : Γ.lookup e = some c)
    (hh : c.protocol.unfold = .sendEndpoint f.role k t s)
    (hv : Γ.lookup f = some v) (hvt : v.Equivalent ⟨k, t⟩) (hne : e ≠ f)
    (hp : HasType n ((Γ.erase f).insert e ⟨c.rank, s⟩) p)
    (hq : HasType n Θ (.inp e.name q)) (hb : f.name.ClosedAt n)
    (hco : Compatible (Γ ∪ Θ)) :
    ∃ d t' u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvEndpoint f.role k t' u ∧ t'.TreeEquiv t ∧ u.TreeEquiv s.dual ∧
      HasType n (((Γ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
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
    have hout := HasType.par hsplit hp hright
    rw [Context.transfer_union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hv hne] at hout
    exact ⟨d, t', u, ht, hdual.1, hu, htp, hus, hout⟩

/-- **Head update leaves other lookups unchanged.**
Exact two-insert head updates leave every other actual lookup unchanged,
without requiring the receiver-tail code to equal the sender's dual. -/
theorem head_update_other (Δ : Context) (e x : Key) (c d : Capability)
    (hx : x ≠ e) (hp : x ≠ e.opposite) :
    ((Δ.insert e c).insert e.opposite d).lookup x = Δ.lookup x := by
  rw [Finmap.lookup_insert_of_ne _ hp, Finmap.lookup_insert_of_ne _ hx]

private theorem out_full_inv {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : HasType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ b.ClosedAt n ∧
      ((∃ s, c.protocol.unfold = .sendName s ∧ HasType n (Δ.insert e ⟨c.rank, s⟩) p) ∨
       ∃ f v k t s, f.name = b ∧ c.protocol.unfold = .sendEndpoint f.role k t s ∧
         Δ.lookup f = some v ∧ v.Equivalent ⟨k, t⟩ ∧ e ≠ f ∧
         HasType n ((Δ.erase f).insert e ⟨c.rank, s⟩) p) := by
  cases h with
  | outName hc hh ha hb hp => exact ⟨_, _, rfl, hc, hb, Or.inl ⟨_, hh, hp⟩⟩
  | outEndpoint hc hh hv he hne ha hb hp =>
    exact ⟨_, _, rfl, hc, hb, Or.inr ⟨_, _, _, _, _, rfl, hh, hv, he, hne, hp⟩⟩

/-- **Head communication preserves conversion typing.**
A typed opposite-head pair at an initially semantically compatible interface
yields packed literal-head preservation. Both actual heads and payload/tail
correspondence are conclusions, not fields in a protocol or admission predicate. -/
theorem HasType.head_preservation {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : HasType n Δ (.par (.out a b p) (.inp a q))) (hco : Compatible Δ) :
    ∃ e c d s u, e.name = a ∧ Δ.lookup e = some c ∧ Δ.lookup e.opposite = some d ∧
      d.rank = c.rank ∧ u.TreeEquiv s.dual ∧
      ((c.protocol.unfold = .sendName s ∧ d.protocol.unfold = .recvName u) ∨
       ∃ f v k t t', f.name = b ∧ Δ.lookup f = some v ∧ v.Equivalent ⟨k, t⟩ ∧
         c.protocol.unfold = .sendEndpoint f.role k t s ∧
         d.protocol.unfold = .recvEndpoint f.role k t' u ∧ t'.TreeEquiv t) ∧
      HasType n ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q b)) := by
  cases h with
  | @par n Γ Θ ho hi hd hp hq =>
    obtain ⟨e, c, hn, hc, hb, hcase⟩ := out_full_inv hp
    subst a
    have hwhole : (Γ ∪ Θ).lookup e = some c :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
    rcases hcase with ⟨s, hs, hbody⟩ | ⟨f, v, k, t, s, hbn, hs, hv, he, hne, hbody⟩
    · obtain ⟨d, u, ht, hr, hu, heq, hout⟩ := passive_head_preservation hd hc hs hbody hq hb hco
      have hpeer : (Γ ∪ Θ).lookup e.opposite = some d :=
        (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
      exact ⟨e, c, d, s, u, rfl, hwhole, hpeer, hr, heq, Or.inl ⟨hs, hu⟩, hout⟩
    · subst b
      obtain ⟨d, t', u, ht, hr, hu, htp, heq, hout⟩ :=
        endpoint_head_preservation hd hc hs hv he hne hbody hq hb hco
      have hpeer : (Γ ∪ Θ).lookup e.opposite = some d :=
        (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
      have hvwhole : (Γ ∪ Θ).lookup f = some v :=
        (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
      exact ⟨e, c, d, s, u, rfl, hwhole, hpeer, hr, heq,
        Or.inr ⟨f, v, k, t, t', rfl, hvwhole, he, hs, hu, htp⟩, hout⟩

/-- **Head update leaves the transmitted payload slot unchanged.**
A transmitted payload slot is literally unchanged in the combined map;
its peer role may coexist, but it is neither carrier update key. -/
theorem endpoint_payload_after {Γ Θ : Context} {e f : Key} {c v : Capability}
    (hd : Finmap.Disjoint Γ Θ) (hv : Γ.lookup f = some v) (hp : Θ.lookup e.opposite = some c)
    (hne : e ≠ f) (x y : Capability) :
    (((Γ ∪ Θ).insert e x).insert e.opposite y).lookup f = some v := by
  have hf : f ≠ e.opposite := fun h => hd f (Finmap.mem_of_lookup_eq_some hv)
    (h ▸ Finmap.mem_of_lookup_eq_some hp)
  rw [head_update_other _ _ _ _ _ hne.symm hf]
  exact (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv

end Cslib.SessionTypes.Endpoint.Conversion
