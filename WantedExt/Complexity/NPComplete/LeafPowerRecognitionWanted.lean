/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LEAF POWER RECOGNITION is NP-complete

Source:
M. Dupré la Tour, M. Lafond and N. Ndiaye, "Recognizing leaf powers and pairwise compatibility
graphs is NP-complete", Proceedings of the 2026 Annual ACM-SIAM Symposium on Discrete
Algorithms (SODA 2026), 6166-6183, doi:10.1137/1.9781611978971.219 (arXiv:2510.19763;
Section 2: the definition of leaf powers used below; Corollary 1.2: "Recognition of leaf powers"
is NP-complete);
ISGCI (https://www.graphclasses.org/classes/gc_649.html), class leaf power, problem
"Recognition": NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LeafPowerRecognition

/-!
# LEAF POWER RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a leaf power, i.e., is there a tree `T` and an
integer threshold `θ` such that `V` is the set of leaves of `T` and two distinct vertices of `G`
are adjacent exactly when their distance in `T` is at most `θ`?

Dupré la Tour, Lafond and Ndiaye (Section 2): "We say that `G` is a leaf power if there exists a
tree `T` and an integer threshold `θ` such that: The vertex set `V` is the set of the leaves of
`T`. For any pair of distinct vertices `u, v ∈ V`, there is an edge `(u, v) ∈ E` if and only if
the distance between `u` and `v` in `T`, denoted as `d_T(u, v)`, is at most `θ`. Here, `d_T`
represents the distance metric induced by the tree `T`, with two adjacent vertices having a
distance of 1."

The tree has vertex set `Fin m` for some `m`, and `f : Fin n → Fin m` is an injective map
identifying `V` with the set of leaves of `T`; the leaves are the vertices with at most one
neighbour (in a tree with at least two vertices, exactly the vertices of degree `1`; the single
vertex of a one-vertex tree is its leaf). `T` is required to be acyclic and preconnected: for
`m ≥ 1` this is Mathlib's `SimpleGraph.IsTree`, and it also allows the empty tree on `Fin 0`,
which is the leaf root of the graph with no vertices (no nonempty tree has an empty leaf set).
Distances are Mathlib's `SimpleGraph.dist`, the length of a shortest walk. The threshold is a
natural number: a negative threshold gives the edgeless graph, as does `θ = 0`, since distinct
leaves are at distance at least `1`. The tree is not part of the input, and its size is not
bounded.

The graph is simple and given by an edge list on `Fin n`. The paper proves NP-hardness by a
reduction from triangle ordinal clustering and membership in NP by bounding the weights of an
equivalent weighted leaf root (Theorem 1.4). Leaf powers are closed under deleting vertices and
under adding isolated vertices (attach a long pendant path ending in a new leaf), so isolated
vertices do not change the answer and the binary vertex count does not make the problem
succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev LeafPowerRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LeafPowerRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : LeafPowerRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `T` is a leaf root of `G` with threshold `θ`, the vertices of `G` being the leaves `f v` of
`T`: `T` is acyclic and preconnected (a tree, or empty), `f` is injective, the leaves of `T` (the
vertices with at most one neighbour) are exactly the values of `f`, and two distinct vertices of
`G` are adjacent exactly when their leaves are at distance at most `θ` in `T`. -/
def IsLeafRoot {n m : ℕ} (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin m))
    (f : Fin n → Fin m) (θ : ℕ) : Prop :=
  T.IsAcyclic ∧ T.Preconnected ∧ Function.Injective f ∧
    (∀ x, (T.neighborSet x).Subsingleton ↔ x ∈ Set.range f) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ T.dist (f u) (f v) ≤ θ)

/-- The graph of the instance is a leaf power: it has a leaf root for some threshold. -/
def LeafPowerRecognitionFeasible (i : LeafPowerRecognitionInstance) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (f : Fin i.1 → Fin m) (θ : ℕ), IsLeafRoot (Graph i) T f θ

open Classical in
/-- LEAF POWER RECOGNITION as a decision problem over bitstrings. -/
noncomputable def leafPowerRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LeafPowerRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ LeafPowerRecognitionFeasible i)
  | none => false

/-- **LEAF POWER RECOGNITION is NP-complete.** Source: Dupré la Tour, Lafond and Ndiaye (2026),
Corollary 1.2; ISGCI, class `gc_649`. -/
public theorem_wanted leafPowerRecognition_npComplete :
    leafPowerRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L leafPowerRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.LeafPowerRecognition
