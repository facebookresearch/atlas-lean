/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Context
public import CSLibExt.Languages.SessionTypes.Endpoint.FiniteBridge

/-!
# Finite ownership maps for the original passive-name typing judgement

A finite bound records every original channel slot below it, including
completed slots. The existing finite-support theorem supplies such a bound.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- Turn finitely many original channel slots into polarized finite-map
ownership. The supplied rank assignment adds no execution hypothesis. -/
def Context.ofFinite (Γ : Cslib.SessionTypes.Context) (bound : Nat)
    (r : Role) (rank : Nat → Nat) : Context :=
  Finmap.keysLookupEquiv.symm ⟨
    ((Finset.range bound).image (fun i => (⟨.const i, r⟩ : Key)),
      fun e => match e.name with
      | .const i => if e.role = r ∧ i < bound then
          some ⟨rank i, Protocol.ofFinite (Γ i)⟩ else none
      | .var _ => none), by
    rintro ⟨a, s⟩
    cases a with
    | const i =>
      simp only [Option.isSome_ite, Finset.mem_image, Finset.mem_range,
        Key.mk.injEq, PiCalculus.Name.const.injEq, ↓existsAndEq, true_and]
      exact ⟨fun ⟨hr, hb⟩ => ⟨hb, hr.symm⟩, fun ⟨hb, hr⟩ => ⟨hr.symm, hb⟩⟩
    | var i => simp [Finset.mem_image, Key.mk.injEq]⟩

/-- Exact lookup specification for the finite-resource bridge. -/
theorem Context.lookup_ofFinite (Γ : Cslib.SessionTypes.Context) (bound : Nat)
    (r : Role) (rank : Nat → Nat) (e : Key) :
    (ofFinite Γ bound r rank).lookup e = match e.name with
      | .const i => if e.role = r ∧ i < bound then
          some ⟨rank i, Protocol.ofFinite (Γ i)⟩ else none
      | .var _ => none :=
  Finmap.keysLookupEquiv_symm_apply_lookup _ _

/-- Finite bridge ownership has exactly the bounded constant keys. -/
theorem Context.mem_ofFinite (Γ : Cslib.SessionTypes.Context) (bound : Nat)
    (r : Role) (rank : Nat → Nat) (e : Key) :
    e ∈ ofFinite Γ bound r rank ↔
      ∃ i, i < bound ∧ (⟨.const i, r⟩ : Key) = e := by
  rw [← Finmap.mem_keys, ofFinite, Finmap.keysLookupEquiv_symm_apply_keys]
  simp only [Finset.mem_image, Finset.mem_range]

/-- Advancing an original channel advances precisely its finite-map role. -/
theorem Context.ofFinite_advance (Γ : Cslib.SessionTypes.Context)
    (bound a : Nat) (ha : a < bound) (s : SessionType)
    (r : Role) (rank : Nat → Nat) :
    ofFinite (Cslib.SessionTypes.advance Γ a s) bound r rank =
      (ofFinite Γ bound r rank).insert ⟨.const a, r⟩
        ⟨rank a, Protocol.ofFinite s⟩ := by
  apply Finmap.ext_lookup
  rintro ⟨n, t⟩
  cases n with
  | const i =>
    by_cases ht : t = r
    · subst t
      by_cases hi : i = a
      · subst i
        simp [lookup_ofFinite, Cslib.SessionTypes.advance, ha]
      · have he : (⟨.const i, r⟩ : Key) ≠ ⟨.const a, r⟩ := by simp [hi]
        rw [Finmap.lookup_insert_of_ne _ he]
        simp [lookup_ofFinite, Cslib.SessionTypes.advance, hi]
    · have he : (⟨.const i, t⟩ : Key) ≠ ⟨.const a, r⟩ := by simp [ht]
      rw [Finmap.lookup_insert_of_ne _ he]
      simp [lookup_ofFinite, ht]
  | var i =>
    have he : (⟨.var i, t⟩ : Key) ≠ ⟨.const a, r⟩ := by simp
    rw [Finmap.lookup_insert_of_ne _ he]
    simp [lookup_ofFinite]

/-- Opposite finite roles split without duplicating any endpoint key. -/
theorem Context.disjoint_ofFinite (Γ Θ : Cslib.SessionTypes.Context)
    (b c : Nat) (r s : Role) (hr : r ≠ s) (rank rank' : Nat → Nat) :
    Finmap.Disjoint (ofFinite Γ b r rank) (ofFinite Θ c s rank') := by
  intro e he he'
  obtain ⟨i, _, rfl⟩ := (mem_ofFinite Γ b r rank e).mp he
  obtain ⟨j, _, h⟩ := (mem_ofFinite Θ c s rank' _).mp he'
  have hs := congrArg Key.role h
  exact hr hs.symm

/-- Original completed contexts have no active finite-map protocol. -/
theorem Context.completed_ofFinite (Γ : Cslib.SessionTypes.Context) (bound : Nat)
    (r : Role) (rank : Nat → Nat) (hΓ : ∀ i, Γ i = .end) :
    (ofFinite Γ bound r rank).Completed := by
  intro e c hc
  obtain ⟨i, hi, rfl⟩ := (mem_ofFinite Γ bound r rank e).mp
    (Finmap.mem_of_lookup_eq_some hc)
  have hcap : (⟨rank i, Protocol.ofFinite (Γ i)⟩ : Capability) = c := by
    simpa only [lookup_ofFinite, hi, and_self, ↓reduceIte, Option.some.injEq] using hc
  subst c
  simp [Protocol.ofFinite, hΓ i, Protocol.unfold]

end Cslib.SessionTypes.Endpoint
