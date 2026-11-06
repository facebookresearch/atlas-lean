/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RankedCong
public import CSLibExt.Languages.SessionTypes.Endpoint.SubjectReduction

/-!
# Ranked substitution and literal communication at compatible interfaces
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- **Endpoint substitution preserves ranked typing.**
Endpoint substitution transports every ranked subject and payload guard
with freshness derived from the actual linear ownership split. -/
theorem RankedType.subst_endpoint {n : Nat} {Δ : Context} {b : Name}
    {r : Role} {c : Capability} {p : Proc}
    (h : RankedType (n + 1) ((Context.lift 0 Δ).insert ⟨.var 0, r⟩ c) p)
    (hb : b.ClosedAt n) (hfresh : (⟨b, r⟩ : Key) ∉ Δ) :
    RankedType n (Δ.insert ⟨b, r⟩ c) (PiCalculus.subst p b) := by
  have hi := Context.injOn_received_subst (c := c) hfresh
  have ht := h.rename (fun _ ha => hb.subst ha (Nat.zero_le n)) hi
  rw [Context.rekey_received_subst hfresh hi, mapProc_substName] at ht
  exact ht

/-- **Disjoint split supplies freshness for endpoint substitution.**
The transmitted role's non-aliasing is derived, not a readiness premise. -/
theorem RankedType.subst_endpoint_from_split {n : Nat} {Δ Θ : Context}
    {b : Name} {r : Role} {c old next : Capability} {e : Key} {p : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hs : Δ.lookup ⟨b, r⟩ = some c)
    (hr : Θ.lookup e = some old)
    (hp : RankedType (n + 1)
      ((Context.lift 0 (Θ.insert e next)).insert ⟨.var 0, r⟩ c) p)
    (hb : b.ClosedAt n) :
    RankedType n ((Θ.insert e next).insert ⟨b, r⟩ c) (PiCalculus.subst p b) := by
  apply hp.subst_endpoint hb
  exact Context.fresh_insert_owned (Context.fresh_of_disjoint hd hs)
    (Finmap.mem_of_lookup_eq_some hr)

/-- **Inversion of ranked input typing.**
Ranked input inversion retains both literal payload sorts and all guards. -/
theorem RankedType.inp_inv {n : Nat} {Δ : Context} {a : Name} {p : Proc}
    (h : RankedType n Δ (.inp a p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ GuardMin Δ e c.rank ∧
      ((∃ s, c.protocol.unfold = .recvName s ∧
          RankedType (n + 1) (Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)) p) ∨
        ∃ r k t s, c.protocol.unfold = .recvEndpoint r k t s ∧
          RankedType (n + 1)
            ((Context.lift 0 (Δ.insert e ⟨c.rank, s⟩)).insert ⟨.var 0, r⟩ ⟨k, t⟩) p) := by
  cases h with
  | inpName hg hc hs ha hp => exact ⟨_, _, rfl, hc, hg, Or.inl ⟨_, hs, hp⟩⟩
  | inpEndpoint hg hc hs ha hp => exact ⟨_, _, rfl, hc, hg, Or.inr ⟨_, _, _, _, hs, hp⟩⟩

/-- **Inversion of ranked output typing.**
Ranked output inversion retains the pre-transfer active payload check. -/
theorem RankedType.out_inv {n : Nat} {Δ : Context} {a b : Name} {p : Proc}
    (h : RankedType n Δ (.out a b p)) :
    ∃ e c, e.name = a ∧ Δ.lookup e = some c ∧ GuardMin Δ e c.rank ∧
      ((∃ s, c.protocol.unfold = .sendName s ∧
          RankedType n (Δ.insert e ⟨c.rank, s⟩) p) ∨
        ∃ d k t s, d.name = b ∧ c.protocol.unfold = .sendEndpoint d.role k t s ∧
          Δ.lookup d = some ⟨k, t⟩ ∧ e ≠ d ∧
          RankedType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p) := by
  cases h with
  | outName hg hc hs ha hb hp => exact ⟨_, _, rfl, hc, hg, Or.inl ⟨_, hs, hp⟩⟩
  | outEndpoint hg hc hs hd he ha hb hp =>
    exact ⟨_, _, rfl, hc, hg, Or.inr ⟨_, _, _, _, rfl, hs, hd, he, hp⟩⟩

/-- **Passive head communication preserves ranked typing.**
With the stated disjoint ranked split, scoped passive payload and
compatible combined interface, head communication substitutes through the
ranked input body and retains both residual guard derivations. -/
theorem ranked_passive_head {n : Nat} {Δ Θ : Context} {e : Key}
    {c : Capability} {s : Protocol} {b : Name} {p q : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendName s)
    (hp : RankedType n (Δ.insert e ⟨c.rank, s⟩) p)
    (hq : RankedType n Θ (.inp e.name q)) (hb : b.ClosedAt n)
    (hco : Compatible (Δ ∪ Θ)) :
    RankedType n (((Δ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
      (.par p (PiCalculus.subst q b)) := by
  obtain ⟨d, t, hn, ht, hg, hcase⟩ := hq.inp_inv
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
    have hright := Context.disjoint_insert_owned (c := (⟨c.rank, s.dual⟩ : Capability))
      (hleft.symm _ _) (Finmap.mem_of_lookup_eq_some ht)
    have htyped := RankedType.par (hright.symm _ _) hp hr
    rw [Context.union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht)] at htyped
    exact htyped
  · have hhead := passive_dual_head hdual hs
    rw [hhead] at hu
    cases hu

/-- **Endpoint delegation at the head preserves ranked typing.**
With the stated disjoint ranked split, owned non-carrier scoped payload
and compatible combined interface, delegation derives substitution freshness
from that split and retains the combined payload value. -/
theorem ranked_endpoint_head {n k : Nat} {Δ Θ : Context} {e d : Key}
    {c : Capability} {v s : Protocol} {p q : Proc}
    (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (hs : c.protocol.unfold = .sendEndpoint d.role k v s)
    (hv : Δ.lookup d = some ⟨k, v⟩) (hne : e ≠ d)
    (hp : RankedType n ((Δ.erase d).insert e ⟨c.rank, s⟩) p)
    (hq : RankedType n Θ (.inp e.name q)) (hb : d.name.ClosedAt n)
    (hco : Compatible (Δ ∪ Θ)) :
    RankedType n (((Δ ∪ Θ).insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
      (.par p (PiCalculus.subst q d.name)) := by
  obtain ⟨f, t, hn, ht, hg, hcase⟩ := hq.inp_inv
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
    have hsplit := Context.disjoint_transfer (c := (⟨c.rank, s⟩ : Capability))
      (t := (⟨c.rank, s.dual⟩ : Capability)) (u := (⟨k, v⟩ : Capability))
      hd (Finmap.mem_of_lookup_eq_some hc) (Finmap.mem_of_lookup_eq_some ht) hne
    have htyped := RankedType.par hsplit hp hrec
    rw [Context.transfer_union_insert_owned hd (Finmap.mem_of_lookup_eq_some hc)
      (Finmap.mem_of_lookup_eq_some ht) hv hne] at htyped
    exact htyped

/-- **Ranked head communication exposes peers and residual typing.**
A ranked-typed opposite-head pair at an initially compatible interface
yields the actual subject/dual-peer heads, payload metadata and exact ranked
continuation context after literal communication. -/
theorem RankedType.head_comm_faithful {n : Nat} {Δ : Context} {a b : Name}
    {p q : Proc} (h : RankedType n Δ (.par (.out a b p) (.inp a q)))
    (hco : Compatible Δ) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧
      Δ.lookup e.opposite = some c.dual ∧ MatchedOutput Δ e c s b ∧
      RankedType n ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
        (.par p (PiCalculus.subst q b)) := by
  obtain ⟨Θ, Ξ, rfl, hd, ho, hi⟩ := h.par_inv
  have hb : b.ClosedAt n := ho.hasType.closedAt.2.1
  obtain ⟨e, c, hn, hc, hg, hcase⟩ := ho.out_inv
  subst a
  obtain ⟨f, t, hf, ht, _, _⟩ := hi.inp_inv
  have heq := disjoint_subjects_opposite hd hc ht hf.symm
  have hdual := communicating_capabilities_dual hd hc ht hf.symm hco
  subst f
  subst t
  have hwhole : (Θ ∪ Ξ).lookup e = some c :=
    (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc
  have hfresh : e.opposite ∉ Θ := hd.symm _ _ e.opposite (Finmap.mem_of_lookup_eq_some ht)
  have hpeer : (Θ ∪ Ξ).lookup e.opposite = some c.dual :=
    (Finmap.lookup_union_right hfresh).trans ht
  rcases hcase with ⟨s, hs, hp⟩ | ⟨d, k, v, s, hbn, hs, hv, hne, hp⟩
  · exact ⟨e, c, s, rfl, hwhole, hpeer, MatchedOutput.passive hs,
      ranked_passive_head hd hc hs hp hi hb hco⟩
  · have hpd : e.opposite ≠ d := fun he =>
      hfresh (he.symm ▸ Finmap.mem_of_lookup_eq_some hv)
    have hvwhole : (Θ ∪ Ξ).lookup d = some ⟨k, v⟩ :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
    subst b
    exact ⟨e, c, s, rfl, hwhole, hpeer, MatchedOutput.endpoint rfl hs hvwhole hne hpd,
      ranked_endpoint_head hd hc hs hv hne hp hi hb hco⟩

/-- **Ranked head communication yields a dual advance.**
For a ranked-typed opposite-head pair at a compatible initial interface,
the head result yields one faithful update and compatible ranked residual,
not a typing witness manufactured by forgetting the refinement. -/
theorem RankedType.head_comm_advance {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : RankedType n Δ (.par (.out a b p) (.inp a q))) (hco : Compatible Δ) :
    ∃ Ξ, DualAdvance Δ Ξ ∧ RankedType n Ξ (.par p (PiCalculus.subst q b)) ∧ Compatible Ξ := by
  obtain ⟨e, c, s, hn, hc, hp, hm, ht⟩ := h.head_comm_faithful hco
  have ha := DualAdvance.matched hc hp hm.sendsTo
  exact ⟨_, ha, ht, ha.compatible hco⟩

end Cslib.SessionTypes.Endpoint
