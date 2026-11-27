/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/923.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the definition of the conjecture and the statement that it holds.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Sort
import Mathlib.SetTheory.Cardinal.Order
import MathlibExt.Combinatorics.Graph.MycielskiTheorem

/-!
# Rödl's theorem on triangle-free subgraphs

`conjecture_holds` gives a finite chromatic threshold forcing a triangle-free spanning subgraph
whose chromatic number is at least a prescribed natural number.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem923Wanted

open SimpleGraph

/-- **Erdős Problem 923 on triangle-free subgraphs of large chromatic number.** The proposition
asserts that for every natural number $n$ there is a natural number $k$ such that every simple
graph $G$, on any vertex set, whose chromatic number is at least $k$ has a triangle-free subgraph
$H$ on the same vertex set whose chromatic number is at least $n$. Chromatic numbers may be
infinite. -/
def conjecture : Prop :=
  ∀ n : ℕ, ∃ k : ℕ, ∀ (V : Type*) (G : SimpleGraph V),
    (k : ℕ∞) ≤ G.chromaticNumber →
      ∃ H ≤ G, (n : ℕ∞) ≤ H.chromaticNumber ∧ H.CliqueFree 3

-- Color each edge at its smaller endpoint using a coloring of that vertex's neighborhood.
-- Each color gives a triangle-free graph, and the tuple of their colorings colors the union.
private theorem colorable_of_colorable_neighborhoods {V : Type*} (G : SimpleGraph V) {n t : ℕ}
    (localColor : ∀ v, (G.induce (G.neighborSet v)).Colorable t)
    (colorFree : ∀ H ≤ G, H.CliqueFree 3 → H.Colorable n) : G.Colorable (n ^ t) := by
  classical
  let : LinearOrder V := linearOrderOfSTO WellOrderingRel
  let C (v : V) := (localColor v).some
  let arc (i : Fin t) (x y : V) := x < y ∧ ∃ h : G.Adj x y, C x ⟨y, h⟩ = i
  let layer (i : Fin t) := SimpleGraph.fromRel (arc i)
  have sub (i : Fin t) : layer i ≤ G := by
    intro x y h
    rcases h.2 with ⟨_, hxy, _⟩ | ⟨_, hyx, _⟩
    · exact hxy
    · exact hyx.symm
  have free (i : Fin t) : (layer i).CliqueFree 3 := by
    intro s hs
    -- The two larger vertices of a triangle must get different colors at the smallest one.
    let f := s.orderEmbOfFin hs.card_eq
    have forward (p q : Fin 3) (hpq : p < q) : arc i (f p) (f q) := by
      have hlt := f.strictMono hpq
      have hadj := hs.isClique (s.orderEmbOfFin_mem hs.card_eq p)
        (s.orderEmbOfFin_mem hs.card_eq q) hlt.ne
      exact hadj.2.resolve_right fun h => hlt.asymm h.1
    obtain ⟨_, h₀₁, hc₁⟩ := forward 0 1 (by decide)
    obtain ⟨_, h₀₂, hc₂⟩ := forward 0 2 (by decide)
    obtain ⟨_, h₁₂, _⟩ := forward 1 2 (by decide)
    exact (C (f 0)).valid (v := ⟨f 1, h₀₁⟩) (w := ⟨f 2, h₀₂⟩) h₁₂ (hc₁.trans hc₂.symm)
  let D (i : Fin t) := (colorFree _ (sub i) (free i)).some
  have cover {x y : V} (h : G.Adj x y) : ∃ i, (layer i).Adj x y := by
    rcases lt_or_gt_of_ne h.ne with hlt | hgt
    · exact ⟨_, h.ne, Or.inl ⟨hlt, h, rfl⟩⟩
    · exact ⟨_, h.ne, Or.inr ⟨hgt, h.symm, rfl⟩⟩
  let coloring : G.Coloring (Fin t → Fin n) := Coloring.mk (fun v i => D i v) fun h heq => by
    obtain ⟨i, hi⟩ := cover h
    exact (D i).valid hi (congrFun heq i)
  simpa using coloring.colorable

-- In a graph without an (m + 1)-clique, every neighborhood is m-clique-free.
-- Induction therefore bounds the chromatic number if all triangle-free subgraphs are n-colorable.
private theorem exists_color_bound.{u} (n m : ℕ) :
    ∃ k : ℕ, ∀ {V : Type u} (G : SimpleGraph V), G.CliqueFree m →
      (∀ {W : Type u} (H : SimpleGraph W), H ⊑ G → H.CliqueFree 3 → H.Colorable n) →
        G.Colorable k := by
  induction m with
  | zero => exact ⟨0, fun _ h => (not_cliqueFree_zero h).elim⟩
  | succ m ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨n ^ t, fun G hg hcolor => colorable_of_colorable_neighborhoods G (fun v => ?_)
      (fun H hH => hcolor H (.of_le hH))⟩
    apply ht
    · rw [cliqueFree_induce_iff]
      simpa using CliqueFreeOn.of_succ G (G.cliqueFreeOn_univ.mpr hg) (Set.mem_univ v)
    · exact fun H hH => hcolor H (hH.trans (Embedding.induce (G.neighborSet v)).isContained)

-- Take the image of the copy, leaving every vertex outside its image isolated.
private theorem exists_spanning_of_copy {V W : Type*} {G : SimpleGraph V} {F : SimpleGraph W}
    (hFG : F ⊑ G) (hF : F.CliqueFree 3) :
    ∃ H ≤ G, F.chromaticNumber ≤ H.chromaticNumber ∧ H.CliqueFree 3 := by
  obtain ⟨f⟩ := hFG
  refine ⟨F.map f.toEmbedding, f.toHom.map_le,
    chromaticNumber_mono_of_hom (Embedding.map f.toEmbedding F).toHom, ?_⟩
  intro s hs
  obtain ⟨t, ht, _⟩ := (isNClique_map_iff (by decide : 1 < 3)).mp hs
  exact hF t ht

/--
**Rödl's theorem on triangle-free subgraphs.** For every natural number $n$ there is a natural
number $k$ such that every simple graph $G$, on any vertex set, whose chromatic number is at least
$k$ has a triangle-free subgraph $H$ on the same vertex set whose chromatic number is at least
$n$. Chromatic numbers may be infinite.

This answers Erdős Problem 923 affirmatively; it was proved by Rödl.

Source:
Vojtěch Rödl, On the chromatic number of subgraphs of a given graph, Proceedings of the American
Mathematical Society 64 (1977), 370–371, https://doi.org/10.1090/S0002-9939-1977-0469806-4.
Moved from `OpenConjectures/Combinatorics/ErdosProblem923`.
-/
theorem conjecture_holds : conjecture := by
  intro n
  obtain ⟨W, _, F, hfree, hchi⟩ := MetaMathlibExt.mycielski_theorem.{0, 0, 0}.2 n
  obtain ⟨b, hb⟩ := exists_color_bound n (Fintype.card W)
  refine ⟨b + 1, fun V G hG => ?_⟩
  by_cases hc : G.CliqueFree (Fintype.card W)
  · by_contra h
    have bounded := hb G hc fun H hHG hf => by
      obtain ⟨K, hKG, hχ, hK⟩ := exists_spanning_of_copy hHG hf
      have hlt : K.chromaticNumber < n := lt_of_not_ge fun hn => h ⟨K, hKG, hn, hK⟩
      exact chromaticNumber_le_iff_colorable.mp (hχ.trans hlt.le)
    exact (Nat.not_succ_le_self b) (Nat.cast_le.mp (hG.trans bounded.chromaticNumber_le))
  · have htop : (⊤ : SimpleGraph W) ⊑ G := not_free.mp (mt cliqueFree_card_iff_free_top.mpr hc)
    obtain ⟨H, hHG, hFH, hH⟩ := exists_spanning_of_copy (htop.mono_left le_top) hfree
    exact ⟨H, hHG, hchi.trans hFH, hH⟩

end MathlibExt.Combinatorics.ErdosProblem923Wanted
