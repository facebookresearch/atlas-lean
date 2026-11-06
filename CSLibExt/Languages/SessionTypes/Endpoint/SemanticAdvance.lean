/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionCommunication
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAdvance

/-!
# Faithful semantic subject advancement

Actual old lookups and literal unfolded heads determine both new codes.
There is no process, Step, typing, progress or representative field. Endpoint
payload metadata may describe a private payload, not an external owned key.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Conversion

open PiCalculus

/-- **Matching send and receive heads of two capabilities.**
Both literal communication heads, with separate payload equivalence. -/
inductive CommunicationHeads (c d : Capability) (s u : Protocol) : Prop where
  | passive : c.protocol.unfold = .sendName s → d.protocol.unfold = .recvName u →
      CommunicationHeads c d s u
  | endpoint {r : Role} {k : Nat} {t v : Protocol} :
      c.protocol.unfold = .sendEndpoint r k t s →
      d.protocol.unfold = .recvEndpoint r k v u → v.TreeEquiv t → CommunicationHeads c d s u

/-- **Semantic advancement of a communicating endpoint pair.**
Actual old sender/peer values and literal continuations, not raw dual-code
identity. Target is EXACTLY the two actual subject insertions. -/
inductive SemanticAdvance : Context → Context → Prop where
  | matched {Δ : Context} {e : Key} {c d : Capability} {s u : Protocol} :
      Δ.lookup e = some c → Δ.lookup e.opposite = some d → d.Equivalent c.dual →
      CommunicationHeads c d s u → u.TreeEquiv s.dual →
      SemanticAdvance Δ ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨d.rank, u⟩)

/-- **Semantic balance of a linear context.**
Every actual owned key has a semantic dual peer at equal capability rank. -/
def Balanced (Δ : Context) : Prop :=
  ∀ e c, Δ.lookup e = some c → ∃ d, Δ.lookup e.opposite = some d ∧ d.Equivalent c.dual

/-- **Semantic balance implies semantic compatibility.**
Semantic balance supplies semantic compatibility by actual lookup uniqueness. -/
theorem Balanced.compatible {Δ : Context} (h : Balanced Δ) : Compatible Δ := by
  intro e c d hc hd
  obtain ⟨v, hv, hr⟩ := h e c hc
  have he := Context.unique hd hv
  subst d
  exact hr

/-- **The empty context is semantically balanced.**
Empty interface balance is not a completion assertion about private work. -/
theorem balanced_empty : Balanced (∅ : Context) := by
  intro e c hc
  simp at hc

/-- **Raw balance implies semantic balance.**
Literal raw balance is a special case, not the semantic definition. -/
theorem balanced_of_raw {Δ : Context} (h : Endpoint.Balanced Δ) : Balanced Δ :=
  fun e c hc => ⟨c.dual, h e c hc, Capability.Equivalent.refl _⟩

/-- **Semantic advancement preserves the context's domain.**
Exact domain preservation includes completed capabilities. -/
theorem SemanticAdvance.mem_iff {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ) (x : Key) :
    x ∈ Ξ ↔ x ∈ Δ := by
  cases h with
  | matched hc hd he hh ht =>
    rw [Finmap.mem_insert, Finmap.mem_insert]
    constructor
    · rintro (rfl | rfl | hm)
      · exact Finmap.mem_of_lookup_eq_some hd
      · exact Finmap.mem_of_lookup_eq_some hc
      · exact hm
    · exact fun hm => Or.inr (Or.inr hm)

/-- **Semantic advancement preserves disjointness from a frame.**
No new key can conflict with a parallel ownership frame. -/
theorem SemanticAdvance.disjoint_frame {Δ Ξ Θ : Context} (h : SemanticAdvance Δ Ξ)
    (hd : Finmap.Disjoint Δ Θ) : Finmap.Disjoint Ξ Θ :=
  fun e he ht => hd e ((h.mem_iff e).mp he) ht

/-- **Semantic advancement preserves scoping of owned keys.**
Canonical scope of the whole owned domain is preserved. -/
theorem SemanticAdvance.scope {Δ Ξ : Context} {n : Nat} (h : SemanticAdvance Δ Ξ)
    (hs : ∀ e ∈ Δ, e.name.ClosedAt n) : ∀ e ∈ Ξ, e.name.ClosedAt n :=
  fun e he => hs e ((h.mem_iff e).mp he)

private theorem updated_subject (Δ : Context) (e : Key) (c d : Capability) :
    ((Δ.insert e c).insert e.opposite d).lookup e = some c := by
  rw [Finmap.lookup_insert_of_ne _ (fun he => Key.opposite_ne e he.symm), Finmap.lookup_insert]

private theorem reverse_dual_equivalent {c d : Capability} (h : d.Equivalent c.dual) :
    c.Equivalent d.dual := by
  simpa only [Capability.dual_dual] using h.dual.symm

private theorem opposite_not_subjects {x e : Key} (hx : x ≠ e) (hp : x ≠ e.opposite) :
    x.opposite ≠ e ∧ x.opposite ≠ e.opposite := by
  constructor
  · intro he
    exact hp (by simpa only [Key.opposite_opposite] using congrArg Key.opposite he)
  · intro he
    exact hx (by simpa only [Key.opposite_opposite] using congrArg Key.opposite he)

/-- **Semantic advancement preserves compatibility.**
Actual compatible source retains semantic duality after the exact update. -/
theorem SemanticAdvance.compatible {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ)
    (hc : Compatible Δ) : Compatible Ξ := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    have hn : (⟨d.rank, u⟩ : Capability).Equivalent (⟨c.rank, s⟩ : Capability).dual := ⟨he.1, ht⟩
    intro x a b ha hb
    by_cases hx : x = e
    · subst x
      rw [updated_subject] at ha
      rw [Finmap.lookup_insert] at hb
      cases ha
      cases hb
      exact hn
    · by_cases hxp : x = e.opposite
      · subst x
        rw [Finmap.lookup_insert] at ha
        rw [Key.opposite_opposite, updated_subject] at hb
        cases ha
        cases hb
        exact reverse_dual_equivalent hn
      · obtain ⟨hoa, hob⟩ := opposite_not_subjects hx hxp
        rw [head_update_other _ _ _ _ _ hx hxp] at ha
        rw [head_update_other _ _ _ _ _ hoa hob] at hb
        exact hc x a b ha hb

/-- **Semantic advancement preserves balance.**
From a semantically balanced initial interface, actual advancement retains
balance with exact old keys and actual new codes. -/
theorem SemanticAdvance.balanced {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ)
    (hb : Balanced Δ) : Balanced Ξ := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    have hn : (⟨d.rank, u⟩ : Capability).Equivalent (⟨c.rank, s⟩ : Capability).dual := ⟨he.1, ht⟩
    intro x a ha
    by_cases hx : x = e
    · subst x
      rw [updated_subject] at ha
      cases ha
      exact ⟨_, Finmap.lookup_insert _, hn⟩
    · by_cases hxp : x = e.opposite
      · subst x
        rw [Finmap.lookup_insert] at ha
        cases ha
        exact ⟨_, by rw [Key.opposite_opposite]; exact updated_subject _ _ _ _,
          reverse_dual_equivalent hn⟩
      · obtain ⟨hoa, hob⟩ := opposite_not_subjects hx hxp
        rw [head_update_other _ _ _ _ _ hx hxp] at ha
        obtain ⟨b, hp, hr⟩ := hb x a ha
        exact ⟨b, by rw [head_update_other _ _ _ _ _ hoa hob]; exact hp, hr⟩

/-- **Semantic advancement extends from the left part to the whole union.**
Left frame preserves actual old lookups and all literal head evidence. -/
theorem SemanticAdvance.frame_left {Δ Ξ Θ : Context} (h : SemanticAdvance Δ Ξ) :
    SemanticAdvance (Δ ∪ Θ) (Ξ ∪ Θ) := by
  cases h with
  | matched hc hd he hh ht =>
    rw [← Finmap.insert_union, ← Finmap.insert_union]
    exact SemanticAdvance.matched
      ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc)
      ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hd)).trans hd) he hh ht

/-- **Semantic advancement extends from the right part to a disjoint union.**
Right frame uses actual disjointness so neither old subject is shadowed. -/
theorem SemanticAdvance.frame_right {Δ Ξ Θ : Context} (h : SemanticAdvance Δ Ξ)
    (hd : Finmap.Disjoint Θ Δ) : SemanticAdvance (Θ ∪ Δ) (Θ ∪ Ξ) := by
  have ht : Finmap.Disjoint Θ Ξ := (h.disjoint_frame (hd.symm _ _)).symm _ _
  rw [Finmap.union_comm_of_disjoint hd, Finmap.union_comm_of_disjoint ht]
  exact h.frame_left

/-- **Literally dual capabilities have literally dual continuations.**
Literal duality of the ORIGINAL codes forces literal tail equality. -/
theorem CommunicationHeads.literal_dual_tail {c d : Capability} {s u : Protocol}
    (h : CommunicationHeads c d s u) (hd : d = c.dual) : u = s.dual := by
  subst d
  cases h with
  | passive hs hu =>
    have ht : c.dual.protocol.unfold = .recvName s.dual := by
      change c.protocol.dual.unfold = _
      rw [Protocol.unfold_dual, hs]
      rfl
    exact Protocol.recvName.inj (hu.symm.trans ht)
  | @endpoint r k t v hs hu hp =>
    have ht : c.dual.protocol.unfold = .recvEndpoint r k t s.dual := by
      change c.protocol.dual.unfold = _
      rw [Protocol.unfold_dual, hs]
      rfl
    exact (Protocol.recvEndpoint.inj (hu.symm.trans ht)).2.2.2

/-- **Communication heads give a send-head observation.**
The existing raw send-head observation is reused only as a pure head fact. -/
theorem CommunicationHeads.sendsTo {c d : Capability} {s u : Protocol}
    (h : CommunicationHeads c d s u) : SendsTo c s := by
  cases h with
  | passive hs hu => exact Or.inl hs
  | endpoint hs hu hp => exact Or.inr ⟨_, _, _, hs⟩

/-- **Raw dual advancement is a semantic advancement.**
Raw actual dual-code advancement embeds into the semantic relation. -/
theorem SemanticAdvance.of_raw {Δ Ξ : Context} (h : DualAdvance Δ Ξ) : SemanticAdvance Δ Ξ := by
  cases h with
  | @matched e c s hc hd hs =>
    apply SemanticAdvance.matched hc hd (Capability.Equivalent.refl c.dual)
    · rcases hs with hs | ⟨r, k, t, hs⟩
      · apply CommunicationHeads.passive hs
        change c.protocol.dual.unfold = _
        rw [Protocol.unfold_dual, hs]
        rfl
      · apply CommunicationHeads.endpoint hs
        · change c.protocol.dual.unfold = _
          rw [Protocol.unfold_dual, hs]
          rfl
        · exact Protocol.TreeEquiv.refl _
    · exact Protocol.TreeEquiv.refl _

/-- **Semantic advancement is raw under literal compatibility.**
Reverse bridge requires literal ORIGINAL peer compatibility, not merely
semantic compatibility or residual retyping. -/
theorem SemanticAdvance.to_raw {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ)
    (hc : Endpoint.Compatible Δ) : DualAdvance Δ Ξ := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    have hd : d = c.dual := hc e c d hs hp
    have hu := hh.literal_dual_tail hd
    subst d
    subst u
    exact DualAdvance.matched (e := e) (c := c) (s := s) hs hp hh.sendsTo

/-- **Lifting preserves semantic advancement.**
Canonical lifting preserves actual heads, ranks and code-valued payloads. -/
theorem SemanticAdvance.lift {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ) (k : Nat) :
    SemanticAdvance (Context.lift k Δ) (Context.lift k Ξ) := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    rw [Context.lift_insert, Context.lift_insert]
    exact SemanticAdvance.matched (Context.lookup_lift.mpr hs)
      (Context.lookup_lift.mpr hp) he hh ht

/-- **Binder swapping preserves semantic advancement.**
Canonical swapping permutes only subject keys, never the protocol codes. -/
theorem SemanticAdvance.swap {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ) (k : Nat) :
    SemanticAdvance (Context.swap k Δ) (Context.swap k Ξ) := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    rw [Context.swap_insert, Context.swap_insert]
    exact SemanticAdvance.matched (Context.lookup_rekey.mpr ⟨e, hs, rfl⟩)
      (Context.lookup_rekey.mpr ⟨e.opposite, hp, rfl⟩) he hh ht

/-- **Typed head communication yields a semantic advancement.**
A typed opposite-head pair at an initially semantically compatible interface
yields a faithful semantic advance and a compatible typed residual. -/
theorem HasType.head_advance {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : HasType n Δ (.par (.out a b p) (.inp a q))) (hc : Compatible Δ) :
    ∃ Ξ, HasType n Ξ (.par p (PiCalculus.subst q b)) ∧ Compatible Ξ ∧ SemanticAdvance Δ Ξ := by
  obtain ⟨e, c, d, s, u, hn, hs, hp, hr, ht, hh, hout⟩ := h.head_preservation hc
  have hheads : CommunicationHeads c d s u := by
    rcases hh with ⟨hs, hp⟩ | ⟨f, v, k, t, t', hb, hv, hvt, hs, hp, heq⟩
    · exact CommunicationHeads.passive hs hp
    · exact CommunicationHeads.endpoint hs hp heq
  have ha := SemanticAdvance.matched hs hp (hc e c d hs hp) hheads ht
  exact ⟨_, hout, ha.compatible hc, ha⟩

/-- **Semantic advancement preserves capability ranks.**
Every actual capability retains its enclosing rank at the same key. -/
theorem SemanticAdvance.rank_lookup {Δ Ξ : Context} (h : SemanticAdvance Δ Ξ) {x : Key}
    {a b : Capability} (ha : Δ.lookup x = some a) (hb : Ξ.lookup x = some b) : a.rank = b.rank := by
  cases h with
  | @matched e c d s u hs hp he hh ht =>
    by_cases hx : x = e
    · subst x
      have hac := Context.unique ha hs
      subst a
      rw [updated_subject] at hb
      cases hb
      rfl
    · by_cases hxp : x = e.opposite
      · subst x
        have had := Context.unique ha hp
        subst a
        rw [Finmap.lookup_insert] at hb
        cases hb
        rfl
      · rw [head_update_other _ _ _ _ _ hx hxp] at hb
        exact congrArg Capability.rank (Context.unique ha hb)

end Cslib.SessionTypes.Endpoint.Conversion
