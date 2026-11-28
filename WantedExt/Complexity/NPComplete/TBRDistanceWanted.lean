/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TBR DISTANCE is NP-complete

Source:
B. L. Allen and M. Steel, "Subtree transfer operations and their induced metrics on
evolutionary trees", Annals of Combinatorics 5 (2001), 1-15, doi:10.1007/s00026-001-8006-8;
J. Hein, T. Jiang, L. Wang and K. Zhang, "On the complexity of comparing evolutionary trees",
Discrete Applied Mathematics 71 (1996), 153-169, doi:10.1016/S0166-218X(96)00062-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Bioinformatics.Phylogenetics.Splits
public import Mathlib.Order.Partition.Finpartition

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TBRDistance

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

/-!
# TBR DISTANCE is NP-complete

INSTANCE: two unrooted binary phylogenetic trees `T₁`, `T₂` on the same taxon set `X` with
`|X| ≥ 3`, and a natural number `K`. QUESTION: is the tree-bisection-and-reconnection distance `d_TBR(T₁, T₂)` at
most `K`, that is, is there an agreement forest for `T₁`, `T₂` with at most `K + 1` trees?

Trees are the repository's unrooted binary phylogenetic trees (`UnrootedBinaryTree`: a finite
tree whose leaves, the vertices of degree 1, are labeled bijectively by `X`, every other vertex
having degree 3; Allen and Steel, Definition 1.1). The taxa are `X = Fin m`. A tree is given by
its number of vertices `n`, its edge list on `Fin n`, and the list whose `x`-th entry is the
leaf of taxon `x` (`TreeData`); `IsPhyloTree m t` says that the data describe such a tree, and
`toTree` is that tree.

An agreement forest (Allen and Steel, Definition 2.12) is a partition `L₁, …, L_k` of `X` such
that (2) `T₁|Lⱼ = T₂|Lⱼ` for every `j`, and (3) for `i = 1, 2` the minimal subtrees `Tᵢ(Lⱼ)`
of `Tᵢ` connecting the leaves of `Lⱼ` are vertex-disjoint. The partition is a Mathlib
`Finpartition` of `Finset.univ`; the vertices of `T(L)` are the vertices on the path between two
leaves of `L` (`spanVerts`). Condition (2) is stated with quartets (`DisplaysQuartet T a b c d`,
the quartet `ab|cd`): for any four distinct taxa of `Lⱼ`, `T₁` displays `ab|cd` iff `T₂` does.
This is equivalent to (2): for `a, b, c, d ∈ L`, `T|L` displays `ab|cd` iff `T` does, since
the paths between `a, b` and between `c, d` lie in `T(L)` and forced contractions do not change
whether they share a vertex; isomorphic trees display the same quartets; and an unrooted binary
tree is determined up to isomorphism by its quartets (Semple and Steel 2003, Corollary 6.3.8;
`iso_of_displaysQuartet_iff`). When `|Lⱼ| ≤ 3` there is a single tree on `Lⱼ` and no four
distinct taxa.

Allen and Steel, Theorem 2.13, give `d_TBR(T₁, T₂) = m(T₁, T₂)`, the least number of trees of an
agreement forest minus 1, so `d_TBR(T₁, T₂) ≤ K` iff some agreement forest has at most `K + 1`
trees. They state (Section 3) that the proof of Theorem 8 of Hein, Jiang, Wang and Zhang
(NP-hardness of the maximum agreement forest problem) establishes that the TBR-distance problem
is NP-hard. Membership in NP: an agreement forest is a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A tree: the number of vertices `n`, a list of natural pairs read as the edge list on
`Fin n`, and a list of naturals whose `x`-th entry is read as the leaf of taxon `x`. The data
are raw: an edge may repeat, be a loop or have an endpoint outside `Fin n`, and the leaf list
may have any length; `IsPhyloTree m` states when the data describe a tree, and `WellFormed`
requires it of both trees. -/
abbrev TreeData := ℕ × List (ℕ × ℕ) × List ℕ

/-- An instance: the number of taxa `m`, the trees `T₁` and `T₂`, and the bound `K`. -/
abbrev TBRDistanceInstance := ℕ × TreeData × TreeData × ℕ

/-- The graph of tree data, on `Fin n`. -/
abbrev graph (t : TreeData) : SimpleGraph (Fin t.1) :=
  Cslib.Complexity.Karp.edgeGraph t.1 t.2.1

/-- Adjacency in the graph of an edge list is decidable (it is membership in the list). -/
instance (n : ℕ) (es : List (ℕ × ℕ)) :
    DecidableRel (Cslib.Complexity.Karp.edgeGraph n es).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (((u : ℕ), (v : ℕ)) ∈ es ∨ ((v : ℕ), (u : ℕ)) ∈ es)))

/-- The data describe an unrooted binary phylogenetic tree on the taxa `Fin m`: a simple edge
list on `Fin n` whose graph is a tree, a list of `m` distinct leaves that are exactly the
vertices of degree 1, and every other vertex of degree 3. -/
structure IsPhyloTree (m : ℕ) (t : TreeData) : Prop where
  /-- The edge list is simple: no repeats, loops or reversed pairs, endpoints in range. -/
  simple : t.2.1.Nodup ∧
    ∀ e ∈ t.2.1, e.1 < t.1 ∧ e.2 < t.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ t.2.1
  /-- The graph is a tree. -/
  isTree : (graph t).IsTree
  /-- One leaf per taxon. -/
  length : t.2.2.length = m
  /-- The leaves are vertices. -/
  lt : ∀ v ∈ t.2.2, v < t.1
  /-- Distinct taxa have distinct leaves. -/
  nodup : t.2.2.Nodup
  /-- The listed leaves are exactly the vertices of degree 1. -/
  leaf : ∀ v : Fin t.1, (graph t).degree v = 1 ↔ (v : ℕ) ∈ t.2.2
  /-- Every other vertex has degree 3. -/
  three : ∀ v : Fin t.1, (graph t).degree v ≠ 1 → (graph t).degree v = 3

/-- The leaf of taxon `x`. -/
def leafOf {m : ℕ} {t : TreeData} (h : IsPhyloTree m t) (x : Fin m) :
    {v : Fin t.1 // (graph t).degree v = 1} :=
  ⟨⟨t.2.2[x.val]'(by rw [h.length]; exact x.isLt), h.lt _ (List.getElem_mem _)⟩,
    (h.leaf _).2 (List.getElem_mem _)⟩

/-- Taxa and leaves correspond one to one. -/
theorem leafOf_bijective {m : ℕ} {t : TreeData} (h : IsPhyloTree m t) :
    Function.Bijective (leafOf h) := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun v : {v : Fin t.1 // (graph t).degree v = 1} => (v.1 : ℕ)) hxy
    simp only [leafOf] at h1
    exact Fin.ext ((h.nodup.getElem_inj_iff).1 h1)
  · rintro ⟨v, hv⟩
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem ((h.leaf v).1 hv)
    exact ⟨⟨k, h.length ▸ hk⟩, Subtype.ext (Fin.ext hkv)⟩

/-- The unrooted binary phylogenetic tree described by the data. -/
noncomputable def toTree {m : ℕ} {t : TreeData} (h : IsPhyloTree m t) :
    UnrootedBinaryTree (Fin m) where
  V := Fin t.1
  G := graph t
  isTree := h.isTree
  label := Equiv.ofBijective (leafOf h) (leafOf_bijective h)
  degree_eq_three := h.three

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The vertices of the minimal subtree `T(L)` connecting the leaves of `L`: those on the path
between the leaves of two (not necessarily distinct) taxa of `L`. -/
def spanVerts (T : UnrootedBinaryTree X) (L : Finset X) : Set T.V :=
  {v | ∃ x ∈ L, ∃ y ∈ L, ∃ p : T.G.Walk (T.label x : T.V) (T.label y : T.V),
    p.IsPath ∧ v ∈ p.support}

/-- The partition `F` of the taxa is an agreement forest for `T₁` and `T₂`: on each part `L`,
`T₁` and `T₂` display the same quartets on four distinct taxa of `L` (`T₁|L = T₂|L`), and for
`i = 1, 2` the subtrees `Tᵢ(L)` of distinct parts are vertex-disjoint. -/
def IsAgreementForest (T₁ T₂ : UnrootedBinaryTree X)
    (F : Finpartition (Finset.univ : Finset X)) : Prop :=
  (∀ L ∈ F.parts, ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, ∀ d ∈ L, [a, b, c, d].Nodup →
    (DisplaysQuartet T₁ a b c d ↔ DisplaysQuartet T₂ a b c d)) ∧
  ∀ L ∈ F.parts, ∀ L' ∈ F.parts, L ≠ L' →
    Disjoint (spanVerts T₁ L) (spanVerts T₁ L') ∧ Disjoint (spanVerts T₂ L) (spanVerts T₂ L')

/-- Well-formedness of an instance: there are at least three taxa, and both trees are unrooted
binary phylogenetic trees on the taxa `Fin m`. -/
def WellFormed (i : TBRDistanceInstance) : Prop :=
  3 ≤ i.1 ∧ IsPhyloTree i.1 i.2.1 ∧ IsPhyloTree i.1 i.2.2.1

/-- Some agreement forest for `T₁` and `T₂` has at most `K + 1` trees. -/
def TBRDistanceFeasible (i : TBRDistanceInstance) : Prop :=
  ∃ (h₁ : IsPhyloTree i.1 i.2.1) (h₂ : IsPhyloTree i.1 i.2.2.1)
    (F : Finpartition (Finset.univ : Finset (Fin i.1))),
    F.parts.card ≤ i.2.2.2 + 1 ∧ IsAgreementForest (toTree h₁) (toTree h₂) F

open Classical in
/-- TBR DISTANCE as a decision problem over bitstrings. -/
noncomputable def tbrDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TBRDistanceInstance) x with
  | some i => decide (WellFormed i ∧ TBRDistanceFeasible i)
  | none => false

/-- **TBR DISTANCE is NP-complete.** Source: Allen and Steel (2001), Theorem 2.13 and
Section 3; Hein, Jiang, Wang and Zhang (1996), Theorem 8. -/
public theorem_wanted tbrDistance_npComplete :
    tbrDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L tbrDistanceDec

end MetaMathlibExt.Complexity.NPComplete.TBRDistance
