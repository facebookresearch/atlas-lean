/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.SessionTypes.Endpoint.Protocol
public import Mathlib.Data.Finmap

/-!
# Finite endpoint ownership maps

The canonical Mathlib finite map supplies unique endpoint keys. Parallel
composition additionally requires key-disjointness; left-biased union alone
is not a linear split.
-/

@[expose] public section

namespace Cslib.SessionTypes.Endpoint

/-- One linear protocol obligation with its dependency rank. -/
structure Capability where
  rank : Nat
  protocol : Protocol

/-- Finite ownership map, indexed by polarized keys rather than names. -/
abbrev Context := Finmap (fun _ : Key => Capability)

/-- The peer's obligation has the same rank and dual subject protocol. -/
def Capability.dual (c : Capability) : Capability :=
  ⟨c.rank, c.protocol.dual⟩

/-- Capability duality does not change rank or lose protocol information. -/
@[simp] theorem Capability.dual_dual (c : Capability) : c.dual.dual = c := by
  cases c
  simp [dual]

/-- Rekey a finite map when no two owned keys are merged. Global
injectivity is unnecessary, which matters for endpoint substitution. -/
def Context.rekey (f : Key → Key) (Δ : Context)
    (hf : Set.InjOn f {e | e ∈ Δ}) : Context where
  entries := Δ.entries.map (fun x => ⟨f x.1, x.2⟩)
  nodupKeys := by
    apply Multiset.nodup_keys.mp
    have h := Multiset.Nodup.map_on hf Δ.nodupKeys.nodup_keys
    simpa [Multiset.keys, Multiset.map_map, Function.comp_def] using h

/-- Rekeying has precisely the image of the original owned keys. -/
theorem Context.mem_rekey {f : Key → Key} {Δ : Context}
    {hf : Set.InjOn f {e | e ∈ Δ}} {e : Key} :
    e ∈ rekey f Δ hf ↔ ∃ d ∈ Δ, f d = e := by
  simp only [Finmap.mem_def, rekey, Multiset.keys, Multiset.map_map,
    Multiset.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨x, hx, he⟩
    exact ⟨x.1, ⟨x, hx, rfl⟩, he⟩
  · rintro ⟨d, ⟨x, hx, rfl⟩, he⟩
    exact ⟨x, hx, he⟩

/-- Rekeying preserves each capability verbatim at its image key. -/
theorem Context.lookup_rekey {f : Key → Key} {Δ : Context}
    {hf : Set.InjOn f {e | e ∈ Δ}} {e : Key} {c : Capability} :
    (rekey f Δ hf).lookup e = some c ↔
      ∃ d, Δ.lookup d = some c ∧ f d = e := by
  rw [Finmap.lookup_eq_some_iff]
  change (⟨e, c⟩ : Sigma (fun _ : Key => Capability)) ∈
    Δ.entries.map (fun x => ⟨f x.1, x.2⟩) ↔ _
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨⟨d, t⟩, ht, he⟩
    have hk := congrArg Sigma.fst he
    have hc := congrArg (fun x : Sigma (fun _ : Key => Capability) => x.2) he
    dsimp at hk hc
    subst t
    exact ⟨d, Finmap.lookup_eq_some_iff.mpr ht, hk⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, c⟩, Finmap.lookup_eq_some_iff.mp hd, rfl⟩

/-- Disjoint ownership remains disjoint when the combined owned domain
is rekeyed injectively. Opposite roles are not collapsed to physical names. -/
theorem Context.disjoint_rekey {f : Key → Key} {Δ Θ : Context}
    (hΔ : Set.InjOn f {e | e ∈ Δ}) (hΘ : Set.InjOn f {e | e ∈ Θ})
    (hf : Set.InjOn f {e | e ∈ Δ ∨ e ∈ Θ})
    (hd : Finmap.Disjoint Δ Θ) :
    Finmap.Disjoint (rekey f Δ hΔ) (rekey f Θ hΘ) := by
  intro e he hΘe
  obtain ⟨x, hx, hxe⟩ := mem_rekey.mp he
  obtain ⟨y, hy, hye⟩ := mem_rekey.mp hΘe
  have hxy : x = y := hf (Or.inl hx) (Or.inr hy) (hxe.trans hye.symm)
  exact hd x hx (hxy.symm ▸ hy)

/-- Two lookups of the same linear key cannot give different capabilities. -/
theorem Context.unique {Δ : Context} {e : Key} {c d : Capability}
    (hc : Δ.lookup e = some c) (hd : Δ.lookup e = some d) : c = d :=
  Option.some.inj (hc.symm.trans hd)

/-- A context has no remaining communication obligation. End capabilities
may still be recorded, but an active protocol is never silently discarded. -/
def Context.Completed (Δ : Context) : Prop :=
  ∀ e c, Δ.lookup e = some c → c.protocol.unfold = .done

/-- The empty ownership map is completed. -/
theorem Context.completed_empty : Completed (∅ : Context) := by
  intro e c h
  simp at h

/-- Consecutive collision-free rekeyings compose on the same finite map. -/
theorem Context.rekey_rekey {f g : Key → Key} {Δ : Context}
    (hf : Set.InjOn f {e | e ∈ Δ})
    (hg : Set.InjOn g {e | e ∈ rekey f Δ hf})
    (hgf : Set.InjOn (g ∘ f) {e | e ∈ Δ}) :
    rekey g (rekey f Δ hf) hg = rekey (g ∘ f) Δ hgf := by
  apply Finmap.ext
  simp only [rekey, Multiset.map_map]
  rfl

/-- Identity rekeying retains the exact finite map, including end slots. -/
theorem Context.rekey_id (Δ : Context) (hi : Set.InjOn id {e | e ∈ Δ}) :
    rekey id Δ hi = Δ := by
  apply Finmap.ext
  simp [rekey]

/-- Rekeying that fixes all owned keys retains the exact map. -/
theorem Context.rekey_eq {f : Key → Key} {Δ : Context}
    (hf : Set.InjOn f {e | e ∈ Δ}) (hfix : ∀ e ∈ Δ, f e = e) :
    rekey f Δ hf = Δ := by
  apply Finmap.ext
  change Δ.entries.map (fun x => ⟨f x.1, x.2⟩) = Δ.entries
  calc
    _ = Δ.entries.map id := by
      apply Multiset.map_congr rfl
      rintro ⟨e, c⟩ he
      have hm : e ∈ Δ := Multiset.mem_map_of_mem Sigma.fst he
      simp only [hfix e hm, id_eq]
    _ = _ := Multiset.map_id _

/-- Completed protocols remain completed under collision-free name transport. -/
theorem Context.Completed.rekey {f : Key → Key} {Δ : Context}
    (h : Δ.Completed) (hf : Set.InjOn f {e | e ∈ Δ}) :
    (Context.rekey f Δ hf).Completed := by
  intro e c hc
  obtain ⟨d, hd, _⟩ := Context.lookup_rekey.mp hc
  exact h d c hd

/-- Recording a completed endpoint preserves completion of a finite map. -/
theorem Context.Completed.insert {Δ : Context} {e : Key} {c : Capability}
    (hΔ : Δ.Completed) (hc : c.protocol.unfold = .done) :
    Context.Completed (Δ.insert e c) := by
  intro d t ht
  by_cases he : d = e
  · subst d
    simp only [Finmap.lookup_insert, Option.some.injEq] at ht
    subst t
    exact hc
  · rw [Finmap.lookup_insert_of_ne _ he] at ht
    exact hΔ d t ht

/-- Erasing a key preserves absence of any noncompleted obligation;
the empty map is not itself a completion claim about hidden ν processes. -/
theorem Context.Completed.erase {Δ : Context} {e : Key} (h : Δ.Completed) :
    Context.Completed (Δ.erase e) := by
  intro d c hc
  by_cases he : d = e
  · subst d
    simp at hc
  · rw [Finmap.lookup_erase_ne he] at hc
    exact h d c hc

end Cslib.SessionTypes.Endpoint
