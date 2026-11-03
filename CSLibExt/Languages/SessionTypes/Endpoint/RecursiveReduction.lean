/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.RuntimeReduction
public import CSLibExt.Languages.SessionTypes.Endpoint.PersistentOffers
public import CSLibExt.Languages.SessionTypes.Endpoint.RecursiveRepeatability

/-!
# Actual recursive phases through general runtime preservation

Only initial concrete ownership is used to type reachable trace states. The
literal self-loop codes make actual faithful interface advancement exact identity.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint.Runtime

open PiCalculus

private theorem recurring_peer (b : Name) (r : Role) :
    (recurringInterface b r).lookup ⟨b, r.opposite⟩ = some recurringCap.dual := by
  rw [recurringInterface, Finmap.lookup_union_right (by
    cases r <;> simp [Finmap.mem_singleton, Role.opposite]), Finmap.lookup_singleton_eq]

private theorem recurring_owner (b : Name) (r : Role) :
    (recurringInterface b r).lookup ⟨b, r⟩ = some recurringCap := by
  rw [recurringInterface,
    Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl), Finmap.lookup_singleton_eq]

private theorem recurring_lookup_cases {b : Name} {r : Role} {e : Key} {c : Capability}
    (hc : (recurringInterface b r).lookup e = some c) :
    (e = ⟨b, r⟩ ∧ c = recurringCap) ∨ (e = ⟨b, r.opposite⟩ ∧ c = recurringCap.dual) := by
  by_cases hm : e ∈ (Finmap.singleton ⟨b, r⟩ recurringCap : Context)
  · rw [recurringInterface, Finmap.lookup_union_left hm] at hc
    have he := (Finmap.mem_singleton _ _ _).mp hm
    subst e
    rw [Finmap.lookup_singleton_eq] at hc
    cases hc
    exact Or.inl ⟨rfl, rfl⟩
  · rw [recurringInterface, Finmap.lookup_union_right hm] at hc
    have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hc)
    subst e
    rw [Finmap.lookup_singleton_eq] at hc
    cases hc
    exact Or.inr ⟨rfl, rfl⟩

/-- Both literal opposite-role self-loop slots form an ACTUAL balanced initial
interface; balance is derived from lookup/code facts, not a ready-pair hypothesis. -/
theorem recurring_balanced (b : Name) (r : Role) :
    Conversion.Balanced (recurringInterface b r) := by
  intro e c hc
  rcases recurring_lookup_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨recurringCap.dual, recurring_peer b r, Capability.Equivalent.refl _⟩
  · exact ⟨recurringCap, by
      change (recurringInterface b r).lookup ⟨b, r.opposite.opposite⟩ = some recurringCap
      rw [Role.opposite_opposite]
      exact recurring_owner b r, by
      simpa only [Capability.dual_dual] using Capability.Equivalent.refl recurringCap⟩

/-- EVERY faithful advance of this actual literal self-loop interface is exact
identity. This is a code-level property of the concrete regular cursors, not a
claim that arbitrary equivalent recursive codes stay syntactically unchanged. -/
theorem recurring_advance_identity {b : Name} {r : Role} {Ξ : Context}
    (h : Conversion.SemanticAdvance (recurringInterface b r) Ξ) : Ξ = recurringInterface b r := by
  cases h with
  | @matched e c d s u hc hd he hh ht =>
    rcases recurring_lookup_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hdc := Context.unique hd (recurring_peer b r)
      subst d
      cases hh with
      | passive hs hu =>
        change recurringProtocol.unfold = .sendName s at hs
        rw [recurring_unfold] at hs
        have hs' := Protocol.sendName.inj hs
        subst s
        change recurringProtocol.dual.unfold = .recvName u at hu
        rw [recurring_dual_unfold] at hu
        have hu' := Protocol.recvName.inj hu
        subst u
        change ((recurringInterface b r).insert ⟨b, r⟩ recurringCap).insert
          ⟨b, r.opposite⟩ recurringCap.dual = recurringInterface b r
        rw [Context.insert_of_lookup (recurring_owner b r),
          Context.insert_of_lookup (recurring_peer b r)]
      | endpoint hs hu heq =>
        change recurringProtocol.unfold = .sendEndpoint _ _ _ _ at hs
        rw [recurring_unfold] at hs
        cases hs
    · cases hh with
      | passive hs hu =>
        change recurringProtocol.dual.unfold = .sendName s at hs
        rw [recurring_dual_unfold] at hs
        cases hs
      | endpoint hs hu heq =>
        change recurringProtocol.dual.unfold = .sendEndpoint _ _ _ _ at hs
        rw [recurring_dual_unfold] at hs
        cases hs

/-- ANY actually runtime-typed process at the concrete recurring interface keeps
that EXACT interface after a canonical Step, by GENERAL preservation and the
literal self-loop code property. No phase, readiness or schedule hypothesis. -/
theorem recurring_step_preserved {n : Nat} {p q : Proc} (r : Role) (b : Name)
    (h : HasType n (services r) (recurringInterface b r) p) (hs : PiCalculus.Step p q) :
    HasType n (services r) (recurringInterface b r) q := by
  obtain ⟨Ξ, ht, hc, he⟩ := h.subject_reduction (recurring_balanced b r).compatible hs
  rcases he with rfl | ha
  · exact ht
  · exact recurring_advance_identity ha ▸ ht

/-- GENERAL runtime subject reduction applies to every recursive phase (hence
all THREE phase kinds) in BOTH role orientations, at the exact self-loop interface. -/
theorem phase_step_preserved {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (i : Nat) :
    HasType n (services r) (recurringInterface b r) (phase b (i + 1)) := by
  obtain ⟨Ξ, ht, hc, he⟩ := (phase_typed r b hb hf i).subject_reduction
    (recurring_balanced b r).compatible (phase_step b i)
  rcases he with rfl | ha
  · exact ht
  · exact recurring_advance_identity ha ▸ ht

/-- Every phase's ownership follows from the INITIAL pending typing and GENERAL
finite runtime preservation, not repeated application of concrete phase typing. -/
theorem phase_typed_by_preservation {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (i : Nat) :
    HasType n (services r) (recurringInterface b r) (phase b i) := by
  obtain ⟨Ξ, ht, hc, ha⟩ := (pending_typed r b hb hf).reachable
    (recurring_balanced b r).compatible (phase_reachable b i)
  have he : Ξ = recurringInterface b r := by
    clear ht hc
    induction ha with
    | refl => rfl
    | tail ha hs ih => exact recurring_advance_identity (ih ▸ hs)
  exact he ▸ ht

/-- Initial actual replicated daemons supply EVERY declared signature, not just
requests or shared permissions. Availability remains a syntactic predicate. -/
theorem initial_available (b : Name) (r : Role) : Available (services r) (pending b) := by
  intro s sig hs
  have hm := Finmap.mem_of_lookup_eq_some hs
  rcases Finmap.mem_insert.mp hm with he | he
  · subst s
    exact (phase_offers b r 0).2.2
  · have heq := (Finmap.mem_singleton _ _ _).mp he
    subst s
    exact (phase_offers b r 0).1.2

/-- GENERAL persistent-offer reduction closure preserves the real source daemons
through every finite actual prefix of the recursive execution. -/
theorem phase_available_by_reduction (b : Name) (r : Role) (i : Nat) :
    Available (services r) (phase b i) :=
  (initial_available b r).reachable (phase_reachable b i)

/-- EVERY m has one nonzero finite SAME-session trace with all neighbor Steps,
ALL round markers, ownership derived by GENERAL runtime preservation, and actual
persistent availability derived by GENERAL reduction closure at EVERY state. -/
theorem repeatable_trace_preserved {n : Nat} (r : Role) (b : Name) (hb : b.ClosedAt n)
    (hf : EndpointFresh b) (m : Nat) :
    ∃ f : Fin (3 * (m + 1) + 1) → Proc,
      f ⟨0, by omega⟩ = pending b ∧
      f ⟨3 * (m + 1), Nat.lt_succ_self _⟩ = pending b ∧
      (∀ i : Fin (3 * (m + 1)), PiCalculus.Step (f i.castSucc) (f i.succ)) ∧
      (∀ i, HasType n (services r) (recurringInterface b r) (f i)) ∧
      (∀ i, Available (services r) (f i)) ∧
      ∀ j : Fin (m + 1),
        f ⟨3 * j.val + 2, by omega⟩ = bothInvoked b ∧
          f ⟨3 * j.val + 3, by omega⟩ = pending b := by
  refine ⟨fun i => phase b i.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [phase]
  · simp [phase]
  · intro i
    exact phase_step b i.val
  · intro i
    exact phase_typed_by_preservation r b hb hf i.val
  · intro i
    exact phase_available_by_reduction b r i.val
  · intro j
    exact ⟨(session_round_phase b j.val).1, (session_round_phase b j.val).2.1⟩

end Cslib.SessionTypes.Endpoint.Runtime
