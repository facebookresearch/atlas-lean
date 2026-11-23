/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR ARBORICITY TWO RECOGNITION is NP-complete

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity",
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG'96), 234-239 (1996),
doi:10.1515/9780773591134-041 (Section 3, Theorem 3.1: "Linear Arboricity 2 is NP-complete",
for simple graphs, by modifying Péroche's proof for multigraphs);
B. Péroche, "Complexité de l'arboricité linéaire d'un graphe", RAIRO Recherche Opérationnelle
16 (1982), 125-129, doi:10.1051/ro/1982160201251 (Théorème 4);
ISGCI (https://www.graphclasses.org/classes/gc_733.html), class linear arboricity <= 2, problem
"Recognition": NP-complete, citing Shermer.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearArboricityTwoRecognition

/-!
# LINEAR ARBORICITY TWO RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is the linear arboricity of `G` at most `2`, i.e., can
the edges of `G` be partitioned into two linear forests?

Shermer (Section 1): "a linear forest is a forest where each tree is a path", and "the linear
arboricity ... of a graph is the minimum `k` such that the graph can be decomposed into `k` linear
forests". ISGCI (class `gc_733`): "A graph has linear arboricity `≤ 2` if it can be decomposed
into (is the union of) at most 2 forests whose connected components are linear forests (=paths)."

A linear forest is stated as an acyclic graph (Mathlib's `SimpleGraph.IsAcyclic`) in which every
vertex has degree at most `2`: a finite tree all of whose degrees are at most `2` is a path, and
conversely every vertex of a path has degree at most `2`. A decomposition into two linear forests
is a pair of edge-disjoint spanning subgraphs `H₁`, `H₂` on `Fin n` whose union is `G`; either may
be edgeless, which covers "at most 2". Asking for linear arboricity at most `2` rather than
exactly `2` (Shermer's and Péroche's question) changes only the graphs of linear arboricity at most
`1`, the linear forests themselves, which are recognized in polynomial time.

The graph is simple and given by an edge list on `Fin n`. Isolated vertices do not change the
answer, so the binary vertex count does not make the problem succinct.

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
abbrev LinearArboricityTwoRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LinearArboricityTwoRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : LinearArboricityTwoRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- `H` is a linear forest: acyclic, and every vertex has degree at most `2`, so that every
connected component is a path. -/
def IsLinearForest {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  H.IsAcyclic ∧ ∀ v, H.degree v ≤ 2

/-- The edges of the graph split into two linear forests: edge-disjoint spanning subgraphs
`H₁`, `H₂` whose union is the graph. -/
def LinearArboricityTwoRecognitionFeasible (i : LinearArboricityTwoRecognitionInstance) : Prop :=
  ∃ H₁ H₂ : SimpleGraph (Fin i.1), Disjoint H₁ H₂ ∧ H₁ ⊔ H₂ = Graph i ∧
    IsLinearForest H₁ ∧ IsLinearForest H₂

open Classical in
/-- LINEAR ARBORICITY TWO RECOGNITION as a decision problem over bitstrings. -/
noncomputable def linearArboricityTwoRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LinearArboricityTwoRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ LinearArboricityTwoRecognitionFeasible i)
  | none => false

/-- **LINEAR ARBORICITY TWO RECOGNITION is NP-complete.** Source: Shermer (1996), Theorem 3.1;
Péroche (1982), Théorème 4; ISGCI, class `gc_733`. -/
public theorem_wanted linearArboricityTwoRecognition_npComplete :
    linearArboricityTwoRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearArboricityTwoRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.LinearArboricityTwoRecognition
