/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Communication

/-!
# Faithful dual-subject ownership advancement

This relation records only actual old capabilities and matched protocol heads.
It contains no process, reduction, typing or progress result.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

open PiCalculus

/-- The actual payload kind and continuation of a matched output head. -/
inductive MatchedOutput (Δ : Context) (e : Key) (c : Capability)
    (s : Protocol) (b : Name) : Prop where
  | passive : c.protocol.unfold = .sendName s → MatchedOutput Δ e c s b
  | endpoint {d : Key} {k : Nat} {v : Protocol} :
      d.name = b → c.protocol.unfold = .sendEndpoint d.role k v s →
      Δ.lookup d = some ⟨k, v⟩ → e ≠ d → e.opposite ≠ d →
      MatchedOutput Δ e c s b

/-- The old subject's actual head determines its literal continuation,
independently of whether the transmitted endpoint is external or ν-bound. -/
def SendsTo (c : Capability) (s : Protocol) : Prop :=
  c.protocol.unfold = .sendName s ∨
    ∃ r k v, c.protocol.unfold = .sendEndpoint r k v s

/-- The detailed matched output determines the same literal continuation. -/
theorem MatchedOutput.sendsTo {Δ : Context} {e : Key} {c : Capability}
    {s : Protocol} {b : Name} (h : MatchedOutput Δ e c s b) : SendsTo c s := by
  cases h with
  | passive hs => exact Or.inl hs
  | endpoint hn hs hv he hp => exact Or.inr ⟨_, _, _, hs⟩

/-- Only two actually matched dual subject capabilities advance. Payload
ownership transfer is invisible in the combined map; all other entries remain.
The payload can be private to a ν binder, so external advancement records its
protocol head rather than demanding external ownership of that payload. -/
inductive DualAdvance : Context → Context → Prop where
  | matched {Δ : Context} {e : Key} {c : Capability} {s : Protocol} :
      Δ.lookup e = some c → Δ.lookup e.opposite = some c.dual → SendsTo c s →
      DualAdvance Δ ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)

/-- For a typed opposite-head pair at an initially compatible interface,
the packed result retains the literal send head, payload kind and continuation
correspondence instead of hiding an unconstrained protocol. -/
theorem HasType.head_comm_faithful {n : Nat} {Δ : Context} {a b : Name}
    {p q : Proc} (h : HasType n Δ (.par (.out a b p) (.inp a q)))
    (hco : Compatible Δ) :
    ∃ e c s, e.name = a ∧ Δ.lookup e = some c ∧
      Δ.lookup e.opposite = some c.dual ∧ MatchedOutput Δ e c s b ∧
      HasType n ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩)
        (.par p (PiCalculus.subst q b)) := by
  obtain ⟨Θ, Ξ, rfl, hd, ho, hi⟩ := h.par_inv
  have hb : b.ClosedAt n := ho.closedAt.2.1
  obtain ⟨e, c, hn, hc, hcase⟩ := ho.out_inv
  subst a
  obtain ⟨f, t, hf, ht, _⟩ := hi.inp_inv
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
      passive_head_preservation hd hc hs hp hi hb hco⟩
  · have hpd : e.opposite ≠ d := fun he =>
      hfresh (he.symm ▸ Finmap.mem_of_lookup_eq_some hv)
    have hvwhole : (Θ ∪ Ξ).lookup d = some ⟨k, v⟩ :=
      (Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hv)).trans hv
    subst b
    exact ⟨e, c, s, rfl, hwhole, hpeer,
      MatchedOutput.endpoint rfl hs hvwhole hne hpd,
      endpoint_head_preservation hd hc hs hv hne hp hi hb hco⟩

/-- Outside the two matched subjects, the entire capability is unchanged. -/
theorem dual_update_lookup_other (Δ : Context) (e x : Key) (c : Capability) (s : Protocol)
    (hx : x ≠ e) (hp : x ≠ e.opposite) :
    ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩).lookup x = Δ.lookup x := by
  rw [Finmap.lookup_insert_of_ne _ hp, Finmap.lookup_insert_of_ne _ hx]

/-- The matched subject's rank is retained at its exact continuation. -/
theorem dual_update_lookup_subject (Δ : Context) (e : Key) (c : Capability) (s : Protocol) :
    ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩).lookup e =
      some ⟨c.rank, s⟩ := by
  rw [Finmap.lookup_insert_of_ne _ (fun he => Key.opposite_ne e he.symm),
    Finmap.lookup_insert]

/-- Both matched old keys remain owned; the update creates no new key. -/
theorem DualAdvance.mem_iff {Δ Ξ : Context} (h : DualAdvance Δ Ξ) (x : Key) :
    x ∈ Ξ ↔ x ∈ Δ := by
  cases h with
  | matched hc hp hm =>
    rw [Finmap.mem_insert, Finmap.mem_insert]
    constructor
    · rintro (rfl | rfl | hx)
      · exact Finmap.mem_of_lookup_eq_some hp
      · exact Finmap.mem_of_lookup_eq_some hc
      · exact hx
    · intro hx
      exact Or.inr (Or.inr hx)

/-- From a compatible initial interface, updating both subjects to dual
continuations preserves compatibility independently of process typing. -/
theorem dual_update_compatible {Δ : Context} (h : Compatible Δ)
    (e : Key) (c : Capability) (s : Protocol) :
    Compatible ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩) := by
  intro x u v hu hv
  by_cases hx : x = e
  · subst x
    rw [dual_update_lookup_subject] at hu
    rw [Finmap.lookup_insert] at hv
    cases hu
    cases hv
    rfl
  · by_cases hp : x = e.opposite
    · subst x
      rw [Finmap.lookup_insert] at hu
      rw [Key.opposite_opposite, dual_update_lookup_subject] at hv
      cases hu
      cases hv
      simp [Capability.dual, Protocol.dual_dual]
    · have hxe : x.opposite ≠ e := fun he => hp (by
        have ht := congrArg Key.opposite he
        simpa only [Key.opposite_opposite] using ht)
      have hxp : x.opposite ≠ e.opposite := fun he => hx (by
        have ht := congrArg Key.opposite he
        simpa only [Key.opposite_opposite] using ht)
      rw [dual_update_lookup_other Δ e x c s hx hp] at hu
      rw [dual_update_lookup_other Δ e x.opposite c s hxe hxp] at hv
      exact h x u v hu hv

/-- A faithful matched update retains compatibility if the initial
interface is compatible. -/
theorem DualAdvance.compatible {Δ Ξ : Context} (ha : DualAdvance Δ Ξ)
    (h : Compatible Δ) : Compatible Ξ := by
  cases ha with
  | matched => exact dual_update_compatible h _ _ _

/-- Advancing a matched dual pair preserves full balance when the original
interface is balanced, including every untouched opposite-role obligation. -/
theorem dual_update_balanced {Δ : Context} (h : Balanced Δ)
    (e : Key) (c : Capability) (s : Protocol) :
    Balanced ((Δ.insert e ⟨c.rank, s⟩).insert e.opposite ⟨c.rank, s.dual⟩) := by
  intro x u hu
  by_cases hx : x = e
  · subst x
    rw [dual_update_lookup_subject] at hu
    cases hu
    exact Finmap.lookup_insert _
  · by_cases hp : x = e.opposite
    · subst x
      rw [Finmap.lookup_insert] at hu
      cases hu
      rw [Key.opposite_opposite, dual_update_lookup_subject]
      simp [Capability.dual, Protocol.dual_dual]
    · have hxe : x.opposite ≠ e := fun he => hp (by
        have ht := congrArg Key.opposite he
        simpa only [Key.opposite_opposite] using ht)
      have hxp : x.opposite ≠ e.opposite := fun he => hx (by
        have ht := congrArg Key.opposite he
        simpa only [Key.opposite_opposite] using ht)
      rw [dual_update_lookup_other Δ e x c s hx hp] at hu
      rw [dual_update_lookup_other Δ e x.opposite c s hxe hxp]
      exact h x u hu

/-- Faithful subject advancement retains balance if the initial external
interface is balanced. -/
theorem DualAdvance.balanced {Δ Ξ : Context} (ha : DualAdvance Δ Ξ)
    (h : Balanced Δ) : Balanced Ξ := by
  cases ha with
  | matched => exact dual_update_balanced h _ _ _

/-- A typed opposite-head pair at an initially compatible interface yields
a faithful matched update and a compatible typed residual via the packed result. -/
theorem HasType.head_comm_advance {n : Nat} {Δ : Context} {a b : Name} {p q : Proc}
    (h : HasType n Δ (.par (.out a b p) (.inp a q))) (hco : Compatible Δ) :
    ∃ Ξ, DualAdvance Δ Ξ ∧ HasType n Ξ (.par p (PiCalculus.subst q b)) ∧ Compatible Ξ := by
  obtain ⟨e, c, s, hn, hc, hp, hm, ht⟩ := h.head_comm_faithful hco
  have ha := DualAdvance.matched hc hp hm.sendsTo
  exact ⟨_, ha, ht, ha.compatible hco⟩

/-- A matched update leaves a disjoint ownership frame disjoint. -/
theorem DualAdvance.disjoint_frame {Δ Ξ Θ : Context} (h : DualAdvance Δ Ξ)
    (hd : Finmap.Disjoint Δ Θ) : Finmap.Disjoint Ξ Θ := by
  intro e he ht
  exact hd e ((h.mem_iff e).mp he) ht

/-- A left parallel frame retains all its capabilities and the exact
subject head/rank/continuation correspondence of the actual update. -/
theorem DualAdvance.frame_left {Δ Ξ Θ : Context} (h : DualAdvance Δ Ξ) :
    DualAdvance (Δ ∪ Θ) (Ξ ∪ Θ) := by
  cases h with
  | @matched e c s hc hp hm =>
    rw [← Finmap.insert_union, ← Finmap.insert_union]
    exact DualAdvance.matched
      ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc)
      ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hp)).trans hp) hm

/-- A right parallel frame requires the actual disjoint ownership split,
so its matched entries cannot be shadowed by the left-biased union. -/
theorem DualAdvance.frame_right {Δ Ξ Θ : Context} (h : DualAdvance Δ Ξ)
    (hd : Finmap.Disjoint Θ Δ) : DualAdvance (Θ ∪ Δ) (Θ ∪ Ξ) := by
  have hd' : Finmap.Disjoint Θ Ξ := (h.disjoint_frame (hd.symm _ _)).symm _ _
  rw [Finmap.union_comm_of_disjoint hd, Finmap.union_comm_of_disjoint hd']
  exact h.frame_left

end Cslib.SessionTypes.Endpoint
