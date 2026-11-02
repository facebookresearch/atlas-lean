/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Linkages and separators between vertex sets

For vertex sets `A` and `B` of a finite simple graph, an `A`–`B` separator is a vertex set that
meets every walk from `A` to `B`, and an `A`–`B` linkage of size `n` is a family of `n` pairwise
vertex-disjoint paths, each from a vertex of `A` to a vertex of `B`. Menger's theorem (vertex
form) says that the largest linkage and the smallest separator have the same size. This file
proves the easy inequality (every linkage is at most as large as every separator), monotonicity
in the graph, and the case `n = 1`: if every separator is nonempty then a single `A`–`B` path
exists. It does not prove the full max–min equality for sets `A`, `B`.

## Main definitions

* `StatMech.Combinatorics.MfmIsABSeparator G A B S`: `S` meets every walk from `A` to `B`.
* `StatMech.Combinatorics.MfmLinkage G A B n`: `n` pairwise vertex-disjoint `A`–`B` paths.

## Main results

* `StatMech.Combinatorics.mfm_card_le_separator`: weak Menger duality, a linkage of size `n`
  forces every separator to have at least `n` vertices.
* `StatMech.Combinatorics.mfm_isABSeparator_empty_iff`: the empty set separates `A` from `B`
  exactly when no vertex of `A` reaches a vertex of `B`.
* `StatMech.Combinatorics.mfm_exists_linkage_one`: Menger's theorem for `n = 1`.

See also `MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted.menger_vertex_max_min` and
`MetaMathlibExt.menger_vertex` for the full vertex form of Menger's theorem
between two nonadjacent vertices `s`, `t` (internally disjoint paths and `s`–`t` vertex cuts).

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* R. Diestel, *Graph Theory*, 5th ed. (2017), Section 3.3.
-/

@[expose] public section

open Finset

namespace StatMech
namespace Combinatorics

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `S` separates `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B` visits a
vertex of `S`. Vertices of `A ∩ B` must lie in `S` (take the trivial walk). -/
def MfmIsABSeparator (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ (p : G.Walk a b), ∃ v ∈ p.support, v ∈ S

/-- An `A`–`B` linkage of size `n` in `G`: `n` paths, each from a vertex of `A` to a vertex of `B`,
with pairwise disjoint vertex sets. -/
structure MfmLinkage (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  /-- The start vertex of each path. -/
  src : Fin n → V
  /-- The end vertex of each path. -/
  tgt : Fin n → V
  /-- The paths. -/
  walk : ∀ i, G.Walk (src i) (tgt i)
  /-- Each path starts in `A`. -/
  src_mem : ∀ i, src i ∈ A
  /-- Each path ends in `B`. -/
  tgt_mem : ∀ i, tgt i ∈ B
  /-- Each walk is a path. -/
  isPath : ∀ i, (walk i).IsPath
  /-- Distinct paths share no vertex. -/
  disjoint : ∀ ⦃i j⦄, i ≠ j → ∀ v, v ∈ (walk i).support → v ∉ (walk j).support

/-- A linkage in a subgraph `H ≤ G` is a linkage in `G`. -/
def mfm_linkage_mono {H : SimpleGraph V} (h : H ≤ G) {A B : Finset V} {n : ℕ}
    (L : MfmLinkage H A B n) : MfmLinkage G A B n where
  src := L.src
  tgt := L.tgt
  walk i := (L.walk i).mapLe h
  src_mem := L.src_mem
  tgt_mem := L.tgt_mem
  isPath i := by
    rw [Walk.isPath_def, Walk.support_mapLe_eq_support]
    exact (L.isPath i).support_nodup
  disjoint i j hij v hv := by
    rw [Walk.support_mapLe_eq_support] at hv ⊢
    exact L.disjoint hij v hv

omit [Fintype V] [DecidableEq V] in
/-- A separator in `G` is a separator in every subgraph `H ≤ G`. -/
theorem mfm_separator_mono {H : SimpleGraph V} (h : H ≤ G) {A B S : Finset V}
    (hS : MfmIsABSeparator G A B S) : MfmIsABSeparator H A B S := by
  intro a b ha hb p
  obtain ⟨v, hv, hvS⟩ := hS ha hb (p.mapLe h)
  rw [Walk.support_mapLe_eq_support] at hv
  exact ⟨v, hv, hvS⟩

omit [Fintype V] [DecidableEq V] in
/-- **Weak Menger duality.** If `G` has an `A`–`B` linkage of size `n`, every `A`–`B` separator has
at least `n` vertices: each path meets the separator, and disjoint paths meet it in distinct
vertices. This is the easy half of Menger's theorem (K. Menger, 1927). -/
theorem mfm_card_le_separator {A B : Finset V} {n : ℕ}
    (L : MfmLinkage G A B n) {S : Finset V} (hS : MfmIsABSeparator G A B S) :
    n ≤ S.card := by
  classical
  have hchoose : ∀ i : Fin n, ∃ v, v ∈ (L.walk i).support ∧ v ∈ S := by
    intro i
    obtain ⟨v, hv, hvS⟩ := hS (L.src_mem i) (L.tgt_mem i) (L.walk i)
    exact ⟨v, hv, hvS⟩
  choose f hfp hfS using hchoose
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact L.disjoint hne (f i) (hfp i) (hij ▸ hfp j)
  have hsub : (Finset.univ.image f) ⊆ S := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hfS i
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ S.card := Finset.card_le_card hsub

omit [Fintype V] [DecidableEq V] in
/-- If some vertex of `A` reaches some vertex of `B`, every `A`–`B` separator is nonempty. -/
theorem mfm_separator_nonempty_of_reachable {A B S : Finset V}
    (hS : MfmIsABSeparator G A B S) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (h : G.Reachable a b) : S.Nonempty := by
  obtain ⟨p⟩ := h
  obtain ⟨v, _, hvS⟩ := hS ha hb p
  exact ⟨v, hvS⟩

omit [Fintype V] [DecidableEq V] in
/-- The empty set separates `A` from `B` exactly when no vertex of `A` reaches a vertex of `B`. -/
theorem mfm_isABSeparator_empty_iff {A B : Finset V} :
    MfmIsABSeparator G A B ∅ ↔ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Reachable a b := by
  constructor
  · intro hS a ha b hb hr
    obtain ⟨v, hvS⟩ := mfm_separator_nonempty_of_reachable hS ha hb hr
    simp at hvS
  · intro h a b ha hb p
    exact absurd ⟨p⟩ (h a ha b hb)

omit [Fintype V] [DecidableEq V] in
/-- **Menger's theorem for one path.** If every `A`–`B` separator has at least one vertex, `G` has
an `A`–`B` linkage of size one, that is, a path from `A` to `B`. -/
theorem mfm_exists_linkage_one {A B : Finset V}
    (h : ∀ S : Finset V, MfmIsABSeparator G A B S → 1 ≤ S.card) :
    Nonempty (MfmLinkage G A B 1) := by
  classical
  by_contra hcon
  have hempty : MfmIsABSeparator G A B ∅ := by
    rw [mfm_isABSeparator_empty_iff]
    intro a ha b hb hr
    obtain ⟨p⟩ := hr
    apply hcon
    refine ⟨⟨fun _ => a, fun _ => b, fun _ => p.bypass, fun _ => ha, fun _ => hb,
      fun _ => p.bypass_isPath, ?_⟩⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  have := h ∅ hempty
  simp at this

end Combinatorics
end StatMech
