/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CATERPILLAR ARBORICITY AT MOST 2 is NP-complete

Source:
T. C. Shermer, "On rectangle visibility graphs III. External visibility and complexity",
Proceedings of the 8th Canadian Conference on Computational Geometry (CCCG '96), Ottawa (1996),
234-239 (Section 1: definitions of caterpillars, caterpillar forests and caterpillar arboricity;
Theorem 3.2: "Caterpillar Arboricity 2 is NP-complete");
ISGCI (Information System on Graph Classes and their Inclusions), class "caterpillar
arboricity <= 2" (gc_732), problem Recognition, NP-complete, citing Shermer.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo

/-!
# CATERPILLAR ARBORICITY AT MOST 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is the caterpillar arboricity of `G` at most `2`, that
is, can `G` be decomposed into at most two caterpillar forests?

Shermer (Section 1): "A caterpillar is a tree containing a simple path `P(a, b)` such that every
vertex not on `P(a, b)` is distance one from `P(a, b)`. A caterpillar forest is a forest, where
each tree of the forest is a caterpillar." The caterpillar arboricity of `G` is "the minimum `k`
such that the graph can be decomposed into `k` … caterpillar forests". ISGCI (gc_732): "A graph
has caterpillar arboricity <= 2 if it can be decomposed into (is the union of) at most 2 forests
whose connected components are caterpillar[s]". Shermer's Theorem 3.2 calls the problem
"determining if a given graph has caterpillar arboricity 2" (in NP, NP-hardness by reduction
from LINEAR ARBORICITY 2). Whether a graph is a caterpillar forest (caterpillar arboricity at
most `1`) is decidable in polynomial time, so "exactly 2" and "at most 2" (ISGCI's class, stated
here) are polynomially equivalent questions.

`IsCaterpillarForest H`: `H` is acyclic (Mathlib's `SimpleGraph.IsAcyclic`, a forest), and every
connected component `c` (Mathlib's `SimpleGraph.ConnectedComponent`, whose induced subgraph is a
tree of the forest) contains a path `p` (a walk with `SimpleGraph.Walk.IsPath`) such that every
vertex of `c` is on `p` or adjacent to a vertex of `p`. The path lies in `c`, since `c` is
nonempty and its vertices are on or next to `p`. The decomposition is two spanning subgraphs
`H₁, H₂` of `G` with disjoint edge sets (`Disjoint H₁ H₂`) whose union is `G` (`H₁ ⊔ H₂ = G`);
"at most 2" allows `H₂ = ⊥`, the edgeless graph, which is a caterpillar forest. The graph is
given by an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`).

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
abbrev CaterpillarArboricityTwoInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CaterpillarArboricityTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CaterpillarArboricityTwoInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a caterpillar forest: a forest in which every connected component has a path such
that every vertex of the component is on the path or adjacent to a vertex of the path. -/
def IsCaterpillarForest {V : Type*} (H : SimpleGraph V) : Prop :=
  H.IsAcyclic ∧ ∀ c : H.ConnectedComponent, ∃ (a b : V) (p : H.Walk a b), p.IsPath ∧
    ∀ v ∈ c.supp, v ∈ p.support ∨ ∃ w ∈ p.support, H.Adj v w

/-- The graph decomposes into two edge-disjoint caterpillar forests. -/
def CaterpillarArboricityTwoFeasible (i : CaterpillarArboricityTwoInstance) : Prop :=
  ∃ H₁ H₂ : SimpleGraph (Fin i.1), H₁ ⊔ H₂ = Graph i ∧ Disjoint H₁ H₂ ∧
    IsCaterpillarForest H₁ ∧ IsCaterpillarForest H₂

open Classical in
/-- CATERPILLAR ARBORICITY AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def caterpillarArboricityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CaterpillarArboricityTwoInstance) x with
  | some i => decide (WellFormed i ∧ CaterpillarArboricityTwoFeasible i)
  | none => false

/-- **CATERPILLAR ARBORICITY AT MOST 2 is NP-complete.** Source: Shermer (1996), Theorem 3.2;
ISGCI gc_732. -/
public theorem_wanted caterpillarArboricityTwo_npComplete :
    caterpillarArboricityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L caterpillarArboricityTwoDec

end MetaMathlibExt.Complexity.NPComplete.CaterpillarArboricityTwo
