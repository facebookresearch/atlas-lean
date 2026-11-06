/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ConversionTyping
public import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra

/-!
# Pointwise semantic equivalence of actual finite ownership maps

Option.Rel compares matching lookups, so neither missing keys nor changed
capability ranks are equated. Restriction uses the existing multiset filter
with the original finite-map no-duplicate-key invariant.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- **Pointwise equivalence of ownership maps.**
Same lookup domain, identical enclosing capability ranks, and equivalent
protocol trees. No matching split or retyping result is stored. -/
def ContextEquivalent (Δ Ξ : Context) : Prop :=
  ∀ e, Option.Rel Capability.Equivalent (Δ.lookup e) (Ξ.lookup e)

namespace ContextEquivalent

/-- **Reflexivity of ownership-map equivalence.** Reflexivity of actual matching lookups. -/
theorem refl (Δ : Context) : ContextEquivalent Δ Δ := by
  intro e
  cases Δ.lookup e with
  | none => exact Option.Rel.none
  | some c => exact Option.Rel.some (Capability.Equivalent.refl c)

/-- **Lookups transfer along ownership-map equivalence.**
Matching source lookup yields an actual target binding and rank/tree relation. -/
theorem lookup {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) {e : Key} {c : Capability}
    (hc : Δ.lookup e = some c) : ∃ d, Ξ.lookup e = some d ∧ c.Equivalent d := by
  have he := h e
  rw [hc] at he
  cases hd : Ξ.lookup e with
  | none => rw [hd] at he; cases he
  | some d =>
    rw [hd] at he
    cases he with
    | some hr => exact ⟨d, rfl, hr⟩

/-- **Symmetry of ownership-map equivalence.**
Symmetry includes both absent and present endpoints. -/
theorem symm {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) : ContextEquivalent Ξ Δ := by
  intro e
  have he := h e
  generalize ha : Δ.lookup e = a at he ⊢
  generalize hb : Ξ.lookup e = b at he ⊢
  cases he with
  | none => exact Option.Rel.none
  | some hr => exact Option.Rel.some hr.symm

/-- **Transitivity of ownership-map equivalence.**
Transitivity requires the same intermediate lookup, not a chosen representative. -/
theorem trans {Δ Ξ Ω : Context} (h : ContextEquivalent Δ Ξ) (h' : ContextEquivalent Ξ Ω) :
    ContextEquivalent Δ Ω := by
  intro e
  have he := h e
  have he' := h' e
  generalize ha : Δ.lookup e = a at he ⊢
  generalize hb : Ξ.lookup e = b at he he'
  generalize hc : Ω.lookup e = c at he' ⊢
  cases he with
  | none => exact he'
  | some hr =>
    cases he' with
    | some hr' => exact Option.Rel.some (hr.trans hr')

/-- **Equivalent ownership maps have the same keys.** Exact key-domain invariance. -/
theorem mem_iff {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) (e : Key) : e ∈ Δ ↔ e ∈ Ξ := by
  constructor
  · intro he
    obtain ⟨c, hc⟩ := Finmap.mem_iff.mp he
    obtain ⟨d, hd, hr⟩ := h.lookup hc
    exact Finmap.mem_of_lookup_eq_some hd
  · intro he
    obtain ⟨c, hc⟩ := Finmap.mem_iff.mp he
    obtain ⟨d, hd, hr⟩ := h.symm.lookup hc
    exact Finmap.mem_of_lookup_eq_some hd

/-- **Ownership-map equivalence preserves completion.**
Completion invariance uses actual unfolded done, not just empty ownership. -/
theorem completed {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) (hc : Δ.Completed) : Ξ.Completed := by
  intro e d hd
  obtain ⟨c, he, hr⟩ := h.symm.lookup hd
  exact hr.2.done_iff.mpr (hc e c he)

/-- **Ownership-map equivalence preserves key scoping.**
Scope of every actual owned key is unchanged with the exact domain. -/
theorem scope {Δ Ξ : Context} {n : Nat} (h : ContextEquivalent Δ Ξ)
    (hs : ∀ e ∈ Δ, e.name.ClosedAt n) : ∀ e ∈ Ξ, e.name.ClosedAt n := by
  intro e he
  exact hs e ((h.mem_iff e).mpr he)

/-- **Equivalent insertions preserve ownership-map equivalence.**
Corresponding insertions preserve literal rank and semantic type equivalence. -/
theorem insert {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) (e : Key) {c d : Capability}
    (hr : c.Equivalent d) : ContextEquivalent (Δ.insert e c) (Ξ.insert e d) := by
  intro x
  by_cases he : x = e
  · subst x
    simp only [Finmap.lookup_insert]
    exact Option.Rel.some hr
  · simp only [Finmap.lookup_insert_of_ne _ he]
    exact h x

/-- **Erasure preserves ownership-map equivalence.** Both sides erase precisely the same key. -/
theorem erase {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) (e : Key) :
    ContextEquivalent (Δ.erase e) (Ξ.erase e) := by
  intro x
  by_cases he : x = e
  · subst x
    simp only [Finmap.lookup_erase]
    exact Option.Rel.none
  · simp only [Finmap.lookup_erase_ne he]
    exact h x

/-- **Ownership-map equivalence from two-way lookup correspondence.**
Bidirectional actual lookup correspondence suffices for Option.Rel. -/
theorem of_lookups {Δ Ξ : Context}
    (hf : ∀ e c, Δ.lookup e = some c → ∃ d, Ξ.lookup e = some d ∧ c.Equivalent d)
    (hb : ∀ e d, Ξ.lookup e = some d → ∃ c, Δ.lookup e = some c ∧ c.Equivalent d) :
    ContextEquivalent Δ Ξ := by
  intro e
  cases hc : Δ.lookup e with
  | none =>
    cases hd : Ξ.lookup e with
    | none => exact Option.Rel.none
    | some d =>
      obtain ⟨c, he, hr⟩ := hb e d hd
      rw [hc] at he
      cases he
  | some c =>
    obtain ⟨d, hd, hr⟩ := hf e c hc
    rw [hd]
    exact Option.Rel.some hr

/-- **Union preserves ownership-map equivalence.**
Left-biased unions respect equivalent key domains on BOTH sides. -/
theorem union {Γ Γ' Θ Θ' : Context} (hΓ : ContextEquivalent Γ Γ')
    (hΘ : ContextEquivalent Θ Θ') : ContextEquivalent (Γ ∪ Θ) (Γ' ∪ Θ') := by
  intro e
  by_cases he : e ∈ Γ
  · rw [Finmap.lookup_union_left he, Finmap.lookup_union_left ((hΓ.mem_iff e).mp he)]
    exact hΓ e
  · have he' : e ∉ Γ' := fun hm => he ((hΓ.mem_iff e).mpr hm)
    rw [Finmap.lookup_union_right he, Finmap.lookup_union_right he']
    exact hΘ e

/-- **Lifting preserves ownership-map equivalence.**
Canonical binder lift preserves corresponding values and exact domains. -/
theorem lift {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) (k : Nat) :
    ContextEquivalent (Context.lift k Δ) (Context.lift k Ξ) := by
  apply of_lookups
  · intro e c hc
    obtain ⟨a, ha, rfl⟩ := Context.lookup_rekey.mp hc
    obtain ⟨d, hd, hr⟩ := h.lookup ha
    exact ⟨d, Context.lookup_lift.mpr hd, hr⟩
  · intro e d hd
    obtain ⟨a, ha, rfl⟩ := Context.lookup_rekey.mp hd
    obtain ⟨c, hc, hr⟩ := h.symm.lookup ha
    exact ⟨c, Context.lookup_lift.mpr hc, hr.symm⟩

/-- **Binding equivalent fresh pairs preserves ownership-map equivalence.**
A chosen exact dual private pair can be preserved or equivalently changed. -/
theorem bind {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ) {c d : Capability}
    (hr : c.Equivalent d) : ContextEquivalent (Context.bind c Δ) (Context.bind d Ξ) :=
  ((h.lift 0).insert ⟨.var 0, .positive⟩ hr).insert ⟨.var 0, .negative⟩ hr.dual

/-- **Ownership-map equivalence preserves semantic compatibility.**
Semantic compatibility is invariant, including explicit enclosing ranks. -/
theorem compatible {Δ Ξ : Context} (h : ContextEquivalent Δ Ξ)
    (hc : Conversion.Compatible Δ) : Conversion.Compatible Ξ := by
  intro e c d he hp
  obtain ⟨c', he', hr⟩ := h.symm.lookup he
  obtain ⟨d', hp', hs⟩ := h.symm.lookup hp
  exact (hs.trans (hc e c' d' he' hp')).trans hr.dual.symm

end ContextEquivalent

/-- **Projection of an ownership map onto another map's keys.**
Restrict actual target bindings to the exact key domain of a source map.
The implementation is canonical multiset filtering, not a new finite map. -/
def Context.projectKeys (Γ Ξ : Context) : Context where
  entries := Ξ.entries.filter (fun x => x.1 ∈ Γ)
  nodupKeys := by
    apply Multiset.nodup_keys.mp
    exact Multiset.nodup_of_le (Multiset.map_le_map (Multiset.filter_le _ _))
      Ξ.nodupKeys.nodup_keys

/-- **Lookups in a key projection.**
Projection retains precisely the actual target binding at a source key. -/
theorem Context.lookup_projectKeys {Γ Ξ : Context} {e : Key} {c : Capability} :
    (Γ.projectKeys Ξ).lookup e = some c ↔ Ξ.lookup e = some c ∧ e ∈ Γ := by
  simp only [Finmap.lookup_eq_some_iff, projectKeys, Multiset.mem_filter]

/-- **Keys of a projection are the intersection of domains.**
The projected domain is the exact intersection of actual owned domains. -/
theorem Context.mem_projectKeys {Γ Ξ : Context} {e : Key} :
    e ∈ Γ.projectKeys Ξ ↔ e ∈ Ξ ∧ e ∈ Γ := by
  simp only [Finmap.mem_iff, Context.lookup_projectKeys]
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨⟨c, hc⟩, he⟩
  · rintro ⟨⟨c, hc⟩, he⟩
    exact ⟨c, hc, he⟩

/-- **Key projection is absent outside the source domain.**
Outside a source domain the projection is literally absent. -/
theorem Context.projectKeys_none {Γ Ξ : Context} {e : Key} (he : e ∉ Γ) :
    (Γ.projectKeys Ξ).lookup e = none :=
  Finmap.lookup_eq_none.mpr (fun hm => he (Context.mem_projectKeys.mp hm).2)

/-- **Key projection agrees with the target inside the source domain.**
Inside a source domain the actual target value is retained verbatim. -/
theorem Context.projectKeys_lookup {Γ Ξ : Context} {e : Key} (he : e ∈ Γ) :
    (Γ.projectKeys Ξ).lookup e = Ξ.lookup e := by
  cases hc : Ξ.lookup e with
  | none =>
    apply Finmap.lookup_eq_none.mpr
    intro hm
    exact (Finmap.lookup_eq_none.mp hc) (Context.mem_projectKeys.mp hm).1
  | some c => exact Context.lookup_projectKeys.mpr ⟨hc, he⟩

/-- **Equivalence of a union restricts to its left part.**
An equivalent whole map induces an equivalent child with the exact source
key domain; no matching target split is supplied by a caller. -/
theorem ContextEquivalent.project_left {Γ Θ Ξ : Context}
    (h : ContextEquivalent (Γ ∪ Θ) Ξ) : ContextEquivalent Γ (Γ.projectKeys Ξ) := by
  apply ContextEquivalent.of_lookups
  · intro e c hc
    obtain ⟨d, hd, hr⟩ := h.lookup
      ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc)
    exact ⟨d, Context.lookup_projectKeys.mpr ⟨hd, Finmap.mem_of_lookup_eq_some hc⟩, hr⟩
  · intro e d hd
    obtain ⟨he, hm⟩ := Context.lookup_projectKeys.mp hd
    obtain ⟨c, hc⟩ := Finmap.mem_iff.mp hm
    obtain ⟨v, hv, hr⟩ := h.lookup ((Finmap.lookup_union_left hm).trans hc)
    have hdv : v = d := Context.unique hv he
    subst v
    exact ⟨c, hc, hr⟩

/-- **Equivalence of a disjoint union splits into equivalent parts.**
GENERAL split derivation from source disjointness and whole-map equivalence.
It preserves each child domain and the exact target finite-map union. -/
theorem ContextEquivalent.split {Γ Θ Ξ : Context} (h : ContextEquivalent (Γ ∪ Θ) Ξ)
    (hd : Finmap.Disjoint Γ Θ) :
    ∃ Γ' Θ', Ξ = Γ' ∪ Θ' ∧ Finmap.Disjoint Γ' Θ' ∧
      ContextEquivalent Γ Γ' ∧ ContextEquivalent Θ Θ' := by
  refine ⟨Γ.projectKeys Ξ, Θ.projectKeys Ξ, ?_, ?_, h.project_left, ?_⟩
  · apply Finmap.ext_lookup
    intro e
    by_cases hg : e ∈ Γ
    · have hi : e ∈ Ξ := (h.mem_iff e).mp (Finmap.mem_union.mpr (Or.inl hg))
      have hp : e ∈ Γ.projectKeys Ξ := Context.mem_projectKeys.mpr ⟨hi, hg⟩
      rw [Finmap.lookup_union_left hp, Context.projectKeys_lookup hg]
    · have hp : e ∉ Γ.projectKeys Ξ := fun hm => hg (Context.mem_projectKeys.mp hm).2
      rw [Finmap.lookup_union_right hp]
      by_cases ht : e ∈ Θ
      · rw [Context.projectKeys_lookup ht]
      · have hi : e ∉ Ξ := fun hm => by
          have he := (h.mem_iff e).mpr hm
          rcases Finmap.mem_union.mp he with he | he
          · exact hg he
          · exact ht he
        rw [Finmap.lookup_eq_none.mpr hi, Context.projectKeys_none ht]
  · intro e hg ht
    exact hd e (Context.mem_projectKeys.mp hg).2 (Context.mem_projectKeys.mp ht).2
  · have hc : ContextEquivalent (Θ ∪ Γ) Ξ := by
      rw [Finmap.union_comm_of_disjoint (hd.symm _ _)]
      exact h
    exact hc.project_left

/-- **Equivalent capabilities give equivalent singleton maps.**
Equivalent singleton capabilities preserve their exact polarized key. -/
theorem ContextEquivalent.singleton (e : Key) {c d : Capability} (hr : c.Equivalent d) :
    ContextEquivalent (Finmap.singleton e c) (Finmap.singleton e d) := by
  apply ContextEquivalent.of_lookups
  · intro x v hv
    have hx := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
    subst x
    have hc : v = c := Context.unique hv Finmap.lookup_singleton_eq
    subst v
    exact ⟨d, Finmap.lookup_singleton_eq, hr⟩
  · intro x v hv
    have hx := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hv)
    subst x
    have hd : v = d := Context.unique hv Finmap.lookup_singleton_eq
    subst v
    exact ⟨c, Finmap.lookup_singleton_eq, hr⟩

end Cslib.SessionTypes.Endpoint
