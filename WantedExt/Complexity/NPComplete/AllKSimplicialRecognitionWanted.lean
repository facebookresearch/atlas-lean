/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALL-K-SIMPLICIAL GRAPH RECOGNITION is NP-complete for every fixed K ≥ 3

Source:
P. Gambette and S. Vialette, "On restrictions of balanced 2-interval graphs", Graph-Theoretic
Concepts in Computer Science (WG 2007), Lecture Notes in Computer Science 4769 (2007), 55-65,
doi:10.1007/978-3-540-74839-7_6, Theorem 3 (arXiv:0704.1571).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition

/-!
# ALL-K-SIMPLICIAL GRAPH RECOGNITION is NP-complete for every fixed K ≥ 3

Fix an integer `K ≥ 3`.
INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` all-`K`-simplicial, that is, can the neighborhood of each vertex be partitioned
into at most `K` cliques?

Gambette and Vialette (Section 5): "Let `k ∈ ℕ*`. A graph `G = (V, E)` is all-`k`-simplicial if
the neighborhood of each vertex `v ∈ V` can be partitioned into at most `k` cliques"; Theorem 3:
"Recognizing all-`k`-simplicial graphs is NP-complete for `k ≥ 3`" (by a reduction from GRAPH
K-COLORABILITY: the complement of `G` plus a universal vertex). The ISGCI database lists
recognition of the class "all-4-simplicial" (gc_880) as NP-complete, citing them; ISGCI states the
definition with the closed neighborhood ("the closed neighbourhood of every vertex is the union
of at most 4 cliques"), which is equivalent: a vertex is adjacent to all its neighbors, so it can
be added to (or removed from) any one clique of a partition of its neighborhood (or form a clique
by itself when it has no neighbor, as `K ≥ 1`).

`K` is fixed, not part of the input: the decision problem is `allKSimplicialRecognitionDec k`,
and the theorem holds for every `k ≥ 3`. The graph is given by an edge list on `Fin n`. A
partition of the neighborhood of `v` into at most `k` cliques is a labeling `c` of the
neighbors of `v` (the subtype `{a // G.Adj v a}`) by `Fin k` (the parts are the label classes,
some possibly empty) such that two distinct neighbors with the same label are adjacent
(`IsAllKSimplicial`); an empty neighborhood has the empty labeling for every `k`, including
`k = 0`. Membership in NP, although the vertex count `n` is written in binary: isolated vertices
have empty neighborhoods and impose no condition, so the labelings of the neighborhoods of the at
most `2|E|` non-isolated vertices are a certificate of size polynomial in the length of the edge
list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev AllKSimplicialRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : AllKSimplicialRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : AllKSimplicialRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` is all-`k`-simplicial: for every vertex `v`, the neighborhood of `v` is partitioned into
at most `k` cliques, given by a labeling `c` of the neighbors of `v` with `k` labels in which any
two distinct neighbors with the same label are adjacent. -/
def IsAllKSimplicial {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v : Fin n, ∃ c : {a : Fin n // G.Adj v a} → Fin k, ∀ a b : {a : Fin n // G.Adj v a},
    a ≠ b → c a = c b → G.Adj a b

/-- The graph of the instance is all-`k`-simplicial. -/
def AllKSimplicialRecognitionFeasible (k : ℕ) (i : AllKSimplicialRecognitionInstance) : Prop :=
  IsAllKSimplicial k (Graph i)

open Classical in
/-- ALL-K-SIMPLICIAL GRAPH RECOGNITION, for the fixed `k`, as a decision problem over
bitstrings. -/
noncomputable def allKSimplicialRecognitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AllKSimplicialRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ AllKSimplicialRecognitionFeasible k i)
  | none => false

/-- **ALL-K-SIMPLICIAL GRAPH RECOGNITION is NP-complete for every fixed `K ≥ 3`.** Source:
Gambette and Vialette (2007), Theorem 3. -/
public theorem_wanted allKSimplicialRecognition_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    allKSimplicialRecognitionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (allKSimplicialRecognitionDec k)

end MetaMathlibExt.Complexity.NPComplete.AllKSimplicialRecognition
