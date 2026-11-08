/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @vonbo, Avocado
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Degeneracy
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Degeneracy orderings and the degeneracy coloring bound

Every `k`-degenerate finite simple graph has a *degeneracy ordering*: a vertex
ordering in which every vertex has at most `k` later neighbors (Diestel,
§5.1–5.2). Coloring greedily along such an ordering shows that every
`k`-degenerate finite simple graph is `(k + 1)`-colorable.

This file builds on the degeneracy predicates `SimpleGraph.IsDegenerateOn` and
`SimpleGraph.IsDegenerate` from `MathlibExt.Combinatorics.SimpleGraph.Degeneracy`.

## Main results

* `SimpleGraph.IsDegenerate.exists_degeneracyOrdering`: a `k`-degenerate finite
  graph has an injective labelling `e : V → ℕ` with at most `k` later neighbors
  per vertex.
* `SimpleGraph.IsDegenerate.colorable`: a `k`-degenerate finite graph is
  `(k + 1)`-colorable.
* `SimpleGraph.IsDegenerate.chromaticNumber_le`: the chromatic number of a
  `k`-degenerate finite graph is at most `k + 1`.
-/

namespace SimpleGraph

variable {V : Type*} [Finite V]
variable {G : SimpleGraph V} {k l : ℕ}

/-- Every nonempty finite vertex set in a degenerate region contains a vertex of
small degree inside that set. -/
theorem IsDegenerateOn.exists_small_vertex (s : Finset V)
    (h : G.IsDegenerateOn (↑s : Set V) k) (hs : s.Nonempty) :
    ∃ v ∈ s, (G.neighborSet v ∩ ↑s).ncard ≤ k := by
  obtain ⟨v, hv, hdeg⟩ := h (↑s) (Finset.coe_nonempty.mpr hs) Set.Subset.rfl
  exact ⟨v, Finset.mem_coe.mp hv, hdeg⟩

/-- The edgeless graph is `k`-degenerate for every `k`. -/
theorem isDegenerate_bot (k : ℕ) : (⊥ : SimpleGraph V).IsDegenerate k := by
  intro W hWne _
  obtain ⟨v, hv⟩ := hWne
  refine ⟨v, hv, ?_⟩
  have hempty : ((⊥ : SimpleGraph V).neighborSet v ∩ W) = ∅ := by
    ext w
    simp
  rw [hempty, Set.ncard_empty]
  exact Nat.zero_le k

/-- Increasing the degree bound preserves degeneracy. -/
theorem IsDegenerate.mono (h : G.IsDegenerate k) (hkl : k ≤ l) :
    G.IsDegenerate l :=
  IsDegenerateOn.mono h hkl

/-- A global degree bound implies degeneracy. -/
theorem IsDegenerate.of_forall_degree_le [Fintype V] [DecidableRel G.Adj]
    (h : ∀ v, G.degree v ≤ k) : G.IsDegenerate k := by
  intro W hWne _
  obtain ⟨v, hv⟩ := hWne
  refine ⟨v, hv, ?_⟩
  have hsub : (G.neighborSet v ∩ W) ⊆ ↑(G.neighborFinset v) := by
    intro w hw
    simp only [Set.mem_inter_iff, mem_neighborSet, Finset.mem_coe,
      mem_neighborFinset] at hw ⊢
    exact hw.1
  calc (G.neighborSet v ∩ W).ncard ≤ (↑(G.neighborFinset v) : Set V).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = G.degree v := by rw [Set.ncard_coe_finset]; rfl
    _ ≤ k := h v

/-- A degeneracy ordering of `G` with bound `k`: an injective vertex labelling
such that every vertex has at most `k` neighbors with a greater label. -/
def IsDegeneracyOrdering (G : SimpleGraph V) (k : ℕ) (e : V → ℕ) : Prop :=
  Function.Injective e ∧ ∀ v, (G.neighborSet v ∩ {w | e v < e w}).ncard ≤ k

/-- Degeneracy ordering on a finite vertex set: an injective labelling whose
later-neighborhoods inside the set are small. Proved by peeling off a
small-degree vertex and labelling it `0`. -/
theorem IsDegenerateOn.exists_injOn_ordering (s : Finset V)
    (h : G.IsDegenerateOn (↑s : Set V) k) :
    ∃ e : V → ℕ, Set.InjOn e ↑s ∧
      ∀ v ∈ s, (G.neighborSet v ∩ {w ∈ (↑s : Set V) | e v < e w}).ncard ≤ k := by
  classical
  revert h
  refine Finset.strongInductionOn s (fun s IH h => ?_)
  by_cases hs : s.Nonempty
  · obtain ⟨v, hvs, hdeg⟩ := h.exists_small_vertex s hs
    obtain ⟨e', he'inj, he'bound⟩ := IH (s.erase v) (Finset.erase_ssubset hvs)
      (h.of_subset (Finset.coe_subset.mpr (Finset.erase_subset v s)))
    set e : V → ℕ := fun w => if w = v then 0 else e' w + 1 with he
    refine ⟨e, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      simp only [he] at hab
      by_cases ha' : a = v <;> by_cases hb' : b = v
      · exact ha'.trans hb'.symm
      · subst ha'
        rw [ite_eq_left rfl, ite_eq_right hb'] at hab
        exact absurd hab (by omega)
      · subst hb'
        rw [ite_eq_right ha', ite_eq_left rfl] at hab
        exact absurd hab (by omega)
      · rw [ite_eq_right ha', ite_eq_right hb'] at hab
        have heq : e' a = e' b := by omega
        exact he'inj (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨ha', ha⟩))
          (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hb', hb⟩)) heq
    · intro u hus
      by_cases hu : u = v
      · subst hu
        refine (Set.ncard_le_ncard ?_ (Set.toFinite _)).trans hdeg
        intro w hw
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
        exact ⟨hw.1, hw.2.1⟩
      · have hset : ({w ∈ (↑s : Set V) | e u < e w})
            = {w ∈ (↑(s.erase v) : Set V) | e' u < e' w} := by
          simp only [he]
          ext w
          simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_erase]
          rw [ite_eq_right hu]
          by_cases hw : w = v
          · subst hw
            rw [ite_eq_left rfl]
            have hfalse : ¬ e' u + 1 < 0 := by omega
            simp [hfalse]
          · rw [ite_eq_right hw]
            exact ⟨fun ⟨hws, h⟩ => ⟨⟨hw, hws⟩, by omega⟩,
              fun ⟨⟨_, hws⟩, h⟩ => ⟨hws, by omega⟩⟩
        rw [hset]
        exact he'bound u (Finset.mem_erase.mpr ⟨hu, hus⟩)
  · refine ⟨fun _ => 0, ?_, fun v hv => (hs ⟨v, hv⟩).elim⟩
    intro x hx y hy _
    exact (hs ⟨x, Finset.mem_coe.mp hx⟩).elim

/-- Every `k`-degenerate finite graph has a degeneracy ordering. -/
theorem IsDegenerate.exists_degeneracyOrdering (h : G.IsDegenerate k) :
    ∃ e : V → ℕ, G.IsDegeneracyOrdering k e := by
  have := Fintype.ofFinite V
  have huniv : G.IsDegenerateOn (↑(Finset.univ : Finset V)) k := h.isDegenerateOn _
  obtain ⟨e, heinj, hbound⟩ := huniv.exists_injOn_ordering Finset.univ
  have hinj : Function.Injective e := fun a b hab =>
    heinj (Finset.mem_coe.mpr (Finset.mem_univ a))
      (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  refine ⟨e, hinj, fun v => ?_⟩
  have hb := hbound v (Finset.mem_univ v)
  simpa using hb

/-- A degenerate region can be properly colored with `k + 1` colors on that
region. Proved by peeling off a small-degree vertex and reusing a color absent
from its neighborhood. -/
theorem IsDegenerateOn.exists_coloringFun (s : Finset V)
    (h : G.IsDegenerateOn (↑s : Set V) k) :
    ∃ f : V → Fin (k + 1), ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → f a ≠ f b := by
  classical
  revert h
  refine Finset.strongInductionOn s (fun s IH h => ?_)
  by_cases hs : s.Nonempty
  · obtain ⟨v, hvs, hdeg⟩ := h.exists_small_vertex s hs
    obtain ⟨f', hf'⟩ := IH (s.erase v) (Finset.erase_ssubset hvs)
      (h.of_subset (Finset.coe_subset.mpr (Finset.erase_subset v s)))
    set M := (s.erase v).filter (fun w => G.Adj v w) with hM
    have hsub : (↑M : Set V) ⊆ G.neighborSet v ∩ ↑s := by
      intro w hw
      simp only [hM, Finset.mem_coe, Finset.mem_filter, Finset.mem_erase] at hw
      obtain ⟨⟨_, hws⟩, hwadj⟩ := hw
      exact ⟨(G.mem_neighborSet v w).mpr hwadj, Finset.mem_coe.mpr hws⟩
    have hMcard : M.card ≤ k := by
      calc M.card = (↑M : Set V).ncard := (Set.ncard_coe_finset M).symm
        _ ≤ (G.neighborSet v ∩ ↑s).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ k := hdeg
    have hcard : (M.image (fun w => f' w)).card ≤ k :=
      Finset.card_image_le.trans hMcard
    obtain ⟨c, hc⟩ : ∃ c : Fin (k + 1), c ∉ M.image (fun w => f' w) := by
      by_contra hcon
      have hmem : ∀ c, c ∈ M.image (fun w => f' w) := fun c => by
        by_contra hc'
        exact hcon ⟨c, hc'⟩
      have hsubU : Finset.univ ⊆ M.image (fun w => f' w) := fun c _ => hmem c
      have hle := Finset.card_le_card hsubU
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    set f : V → Fin (k + 1) := fun w => if w = v then c else f' w with hf
    refine ⟨f, ?_⟩
    intro a ha b hb hab
    simp only [hf] at *
    by_cases ha' : a = v <;> by_cases hb' : b = v
    · subst ha'; subst hb'
      exact ((G.ne_of_adj hab) rfl).elim
    · subst ha'
      rw [ite_eq_left rfl, ite_eq_right hb']
      intro heq
      apply hc
      rw [heq]
      exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hb', hb⟩, hab⟩, rfl⟩
    · subst hb'
      rw [ite_eq_right ha', ite_eq_left rfl]
      intro heq
      apply hc
      rw [← heq]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨ha', ha⟩, hab.symm⟩, rfl⟩
    · rw [ite_eq_right ha', ite_eq_right hb']
      exact hf' a (Finset.mem_erase.mpr ⟨ha', ha⟩)
        b (Finset.mem_erase.mpr ⟨hb', hb⟩) hab
  · exact ⟨fun _ => 0, fun a ha _ _ _ => (hs ⟨a, ha⟩).elim⟩

/-- Every `k`-degenerate finite graph is `(k + 1)`-colorable (Diestel, §5.1–5.2). -/
theorem IsDegenerate.colorable (h : G.IsDegenerate k) : G.Colorable (k + 1) := by
  have := Fintype.ofFinite V
  have huniv : G.IsDegenerateOn (↑(Finset.univ : Finset V)) k := h.isDegenerateOn _
  obtain ⟨f, hf⟩ := huniv.exists_coloringFun Finset.univ
  exact ⟨Coloring.mk f
    (fun hadj => hf _ (Finset.mem_univ _) _ (Finset.mem_univ _) hadj)⟩

/-- The chromatic number of a `k`-degenerate finite graph is at most `k + 1`. -/
theorem IsDegenerate.chromaticNumber_le (h : G.IsDegenerate k) :
    G.chromaticNumber ≤ k + 1 := by
  have hle := h.colorable.chromaticNumber_le
  simpa using hle

end SimpleGraph

end
