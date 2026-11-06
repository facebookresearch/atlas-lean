/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeSharedHead
public import CSLibExt.Languages.SessionTypes.Endpoint.SemanticAdvance

/-!
# Runtime communication at initially compatible linear interfaces

Linear heads retain separate actual advertised/owned codes and produce the
existing faithful SemanticAdvance. Shared invoke/accept retains exact ownership.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

/-- **Inversion of runtime input on a nonshared subject.**
A nonshared input subject exposes a genuine linear passive or endpoint head.
The shared accept alternative is excluded by actual subject nonalias. -/
theorem HasType.linear_input_inv {n : Nat} {Γ : ServiceEnv} {Δ : Context} {a : Name} {p : Proc}
    (h : HasType n Γ Δ (.inp a p))
    (hn : ∀ s sig, Γ.lookup s = some sig → a ≠ .const s) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧
      ((∃ s, c.protocol.unfold = .recvName s ∧
          HasType (n + 1) Γ (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p) ∨
       ∃ r k t s, c.protocol.unfold = .recvEndpoint r k t s ∧
          HasType (n + 1) Γ
            ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p) := by
  cases h with
  | inpName hg hd hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inl ⟨_, hh, hp⟩⟩
  | inpEndpoint hg hd hc hh ha hp => exact ⟨_, _, rfl, hc, Or.inr ⟨_, _, _, _, hh, hp⟩⟩
  | accept hs hc hscope hd hp => exact False.elim (hn _ _ hs rfl)

/-- **Semantic advance preserves shared-linear separation.**
Faithful semantic advancement preserves shared/linear separation by its
actual owned-domain invariance, including every completed entry. -/
theorem Separated.advance {Γ : ServiceEnv} {Δ Ξ : Context}
    (h : Separated Γ Δ) (ha : Conversion.SemanticAdvance Δ Ξ) : Separated Γ Ξ := by
  intro e c hc s sig hs
  have hm := (ha.mem_iff e).mp (Finmap.mem_of_lookup_eq_some hc)
  obtain ⟨v, hv⟩ := Finmap.mem_iff.mp hm
  exact h e v hv s sig hs

/-- **Passive head communication preserves runtime typing.**
At an INITIALLY compatible disjoint interface, a linear passive head retains
both actual carrier codes and every runtime continuation guard at unchanged Γ. -/
theorem passive_head_preservation {n : Nat} {Γ : ServiceEnv} {Λ Θ : Context}
    {e : Key} {c : Capability} {s : Protocol} {b : Name} {p q : Proc}
    (hd : Finmap.Disjoint Λ Θ) (hsep : Separated Γ Λ) (hc : Λ.lookup e = some c)
    (hh : c.protocol.unfold = .sendName s) (hp : HasType n Γ (Λ.insert e ⟨c.rank, s⟩) p)
    (hq : HasType n Γ Θ (.inp e.name q)) (hb : b.ClosedAt n)
    (hco : Conversion.Compatible (Λ ∪ Θ)) :
    ∃ d u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvName u ∧ u.TreeEquiv s.dual ∧
      HasType n Γ (((Λ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q b)) := by
  obtain ⟨f, d, hn, ht, hcase⟩ := hq.linear_input_inv (hsep e c hc)
  have he := disjoint_subjects_opposite hd hc ht hn.symm
  subst f
  have hdual := Conversion.communicating_equivalent hd hc ht rfl hco
  obtain ⟨u, hu, hur⟩ := Conversion.passive_peer_head hdual hh
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

/-- **Endpoint head communication preserves runtime typing.**
At an INITIALLY compatible split, linear endpoint communication transfers
ACTUAL v and keeps the receiver's independent advertised payload/tail codes.
The Γ-preserving runtime substitution retains all continuation priorities. -/
theorem endpoint_head_preservation {n k : Nat} {Γ : ServiceEnv} {Λ Θ : Context}
    {e f : Key} {c v : Capability} {t s : Protocol} {p q : Proc}
    (hd : Finmap.Disjoint Λ Θ) (hsep : Separated Γ Λ) (hc : Λ.lookup e = some c)
    (hh : c.protocol.unfold = .sendEndpoint f.role k t s)
    (hv : Λ.lookup f = some v) (hvt : v.Equivalent ⟨k, t⟩) (hne : e ≠ f)
    (hp : HasType n Γ ((Λ.erase f).insert e ⟨c.rank, s⟩) p)
    (hq : HasType n Γ Θ (.inp e.name q)) (hb : f.name.ClosedAt n)
    (hco : Conversion.Compatible (Λ ∪ Θ)) :
    ∃ d t' u, Θ.lookup e.opposite = some d ∧ d.rank = c.rank ∧
      d.protocol.unfold = .recvEndpoint f.role k t' u ∧ t'.TreeEquiv t ∧ u.TreeEquiv s.dual ∧
      HasType n Γ (((Λ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)
        (.par p (PiCalculus.subst q f.name)) := by
  obtain ⟨a, d, hn, ht, hcase⟩ := hq.linear_input_inv (hsep e c hc)
  have he := disjoint_subjects_opposite hd hc ht hn.symm
  subst a
  have hdual := Conversion.communicating_equivalent hd hc ht rfl hco
  obtain ⟨t', u, hu, htp, hus⟩ := Conversion.endpoint_peer_head hdual hh
  rcases hcase with ⟨w, hw, hbody⟩ | ⟨r, l, w, z, hw, hbody⟩
  · rw [hu] at hw
    cases hw
  · obtain ⟨hr, hk, hwp, hz⟩ := Protocol.recvEndpoint.inj (hw.symm.trans hu)
    subst r
    subst l
    subst w
    subst z
    have hpayload : v.Equivalent ⟨k, t'⟩ := hvt.trans ⟨rfl, htp.symm⟩
    have hright := hbody.subst_endpoint_from_split (b := f.name) (r := f.role)
      hsep hd hv ht hpayload hb
    have hsplit := Context.disjoint_transfer (c := (⟨c.rank, s⟩ : Capability))
      (t := (⟨d.rank, u⟩ : Capability)) (u := v) hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hne
    have hout := HasType.par hsplit hp hright
    rw [Context.transfer_union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hv hne] at hout
    exact ⟨d, t', u, ht, hdual.1, hu, htp, hus, hout⟩

/-- **Runtime head communication advances or keeps the interface.**
At an INITIALLY semantically compatible linear interface, actual runtime
heads either advance the paired linear subjects faithfully or transfer on a shared
service with the EXACT unchanged interface. Mixed shared/linear heads are excluded
by source separation, not a finite-fragment erasure or supplied result field. -/
theorem HasType.head_advance {n : Nat} {Γ : ServiceEnv} {Δ : Context} {a b : Name} {p q : Proc}
    (h : HasType n Γ Δ (.par (.out a b p) (.inp a q))) (hco : Conversion.Compatible Δ) :
    ∃ Ξ, HasType n Γ Ξ (.par p (PiCalculus.subst q b)) ∧ Conversion.Compatible Ξ ∧
      (Ξ = Δ ∨ Conversion.SemanticAdvance Δ Ξ) := by
  obtain ⟨Λ, Θ, rfl, hd, hout, hin⟩ := h.par_inv
  cases hout with
  | @outName n Γ Λ e c b s p hg hsep hc hh ha hb hp =>
    obtain ⟨d, u, ht, hr, hu, htail, htyped⟩ :=
      passive_head_preservation hd hsep hc hh hp hin hb hco
    have hwhole : (Λ ∪ Θ).lookup e = some c :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
    have hpeer : (Λ ∪ Θ).lookup e.opposite = some d :=
      (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
    have hadvance := Conversion.SemanticAdvance.matched hwhole hpeer
      (hco e c d hwhole hpeer) (Conversion.CommunicationHeads.passive hh hu) htail
    exact ⟨_, htyped, hadvance.compatible hco, Or.inr hadvance⟩
  | @outEndpoint n Γ Λ e f c v k t s p hg hsep hc hh hv he hne ha hb hp =>
    obtain ⟨d, t', u, ht, hr, hu, htp, htail, htyped⟩ :=
      endpoint_head_preservation hd hsep hc hh hv he hne hp hin hb hco
    have hwhole : (Λ ∪ Θ).lookup e = some c :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
    have hpeer : (Λ ∪ Θ).lookup e.opposite = some d :=
      (Finmap.lookup_union_right (hd.symm _ _ _ (Finmap.mem_of_lookup_eq_some ht))).trans ht
    have hadvance := Conversion.SemanticAdvance.matched hwhole hpeer
      (hco e c d hwhole hpeer) (Conversion.CommunicationHeads.endpoint hh hu htp) htail
    exact ⟨_, htyped, hadvance.compatible hco, Or.inr hadvance⟩
  | invoke hs hsep hv hr he hg hb hp =>
    have htyped := HasType.shared_head hs hd (HasType.invoke hs hsep hv hr he hg hb hp) hin
    exact ⟨_, htyped, hco, Or.inl rfl⟩

end Cslib.SessionTypes.Endpoint.Runtime
