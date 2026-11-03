/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.ContextTransport

/-!
# Balanced physical channels with distinct linear roles

Balance is protocol compatibility, not progress. A context alone does not
record the active restricted channels hidden inside a process.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- Every owned role has its opposite role at the same physical name, with
the same rank and the dual protocol. This condition may permit deadlocks. -/
def Balanced (Δ : Context) : Prop :=
  ∀ e c, Δ.lookup e = some c → Δ.lookup e.opposite = some c.dual

/-- An empty external interface is balanced. Internal ν channels still
require their own balanced ownership and are not thereby completed. -/
theorem balanced_empty : Balanced (∅ : Context) := by
  intro e c hc
  simp at hc

/-- A real fresh restriction creates a balanced pair on a single physical name. -/
theorem balanced_bind_empty (c : Capability) : Balanced (Context.bind c ∅) := by
  intro e t he
  rw [Context.bind_empty] at he
  rcases Finmap.mem_lookup_union'.mp he with he | ⟨_, he⟩
  · have hmem := Finmap.mem_of_lookup_eq_some he
    have hk := (Finmap.mem_singleton _ _ _).mp hmem
    subst e
    simp only [Finmap.lookup_singleton_eq, Option.mem_def, Option.some.injEq] at he
    subst t
    exact Context.lookup_bind_negative c ∅
  · have hmem := Finmap.mem_of_lookup_eq_some he
    have hk := (Finmap.mem_singleton _ _ _).mp hmem
    subst e
    simp only [Finmap.lookup_singleton_eq, Option.mem_def, Option.some.injEq] at he
    subst t
    simpa [Key.opposite, Role.opposite] using Context.lookup_bind_positive c ∅

/-- Capture-safe rekeying transports balance when endpoint roles are retained.
The injectivity condition is on owned keys, not on arbitrary passive data. -/
theorem Balanced.rekey {Δ : Context} {f : PiCalculus.Name → PiCalculus.Name}
    (h : Balanced Δ) (hf : Set.InjOn (Key.mapName f) {e | e ∈ Δ}) :
    Balanced (Context.rekey (Key.mapName f) Δ hf) := by
  intro e c hc
  obtain ⟨d, hd, rfl⟩ := Context.lookup_rekey.mp hc
  exact Context.lookup_rekey.mpr ⟨d.opposite, h d c hd, rfl⟩

/-- A partial interface is compatible if opposite roles, WHEN both are
present, have dual protocols. A missing peer is not an enabled-edge witness. -/
def Compatible (Δ : Context) : Prop :=
  ∀ e c d, Δ.lookup e = some c → Δ.lookup e.opposite = some d → d = c.dual

/-- A balanced complete interface supplies compatibility for every present pair. -/
theorem Balanced.compatible {Δ : Context} (h : Balanced Δ) : Compatible Δ := by
  intro e c d hc hd
  exact Context.unique hd (h e c hc)

/-- A dual-compatible pair of physically equal but disjoint owned keys
must be opposite roles. The runtime channel name alone does not supply this. -/
theorem disjoint_subjects_opposite {Δ Θ : Context} {e d : Key} {c t : Capability}
    (hd : Finmap.Disjoint Δ Θ) (hc : Δ.lookup e = some c)
    (ht : Θ.lookup d = some t) (hn : e.name = d.name) : d = e.opposite := by
  apply Key.eq_opposite_of_name_eq hn
  intro he
  exact hd e (Finmap.mem_of_lookup_eq_some hc)
    (he.symm ▸ Finmap.mem_of_lookup_eq_some ht)

/-- Any left subcontext of a compatible interface retains compatibility of
its present pairs; no global-progress assumption is involved. -/
theorem Compatible.union_left {Δ Θ : Context} (h : Compatible (Δ ∪ Θ)) :
    Compatible Δ := by
  intro e c d hc hd
  exact h e c d
    ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hc)).trans hc)
    ((Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hd)).trans hd)

/-- A right child of a disjoint linear split inherits compatibility of
its present pairs from the combined interface. -/
theorem Compatible.union_right {Δ Θ : Context} (h : Compatible (Δ ∪ Θ))
    (hd : Finmap.Disjoint Δ Θ) : Compatible Θ := by
  intro e c d hc ht
  have he : e ∉ Δ := Finmap.Disjoint.symm _ _ hd e (Finmap.mem_of_lookup_eq_some hc)
  have hp : e.opposite ∉ Δ :=
    Finmap.Disjoint.symm _ _ hd e.opposite (Finmap.mem_of_lookup_eq_some ht)
  exact h e c d ((Finmap.lookup_union_right he).trans hc)
    ((Finmap.lookup_union_right hp).trans ht)

end Cslib.SessionTypes.Endpoint
