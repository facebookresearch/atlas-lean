/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on strongly chordal split graphs is NP-complete

Source:
H. Müller, "Hamiltonian circuits in chordal bipartite graphs", Discrete Mathematics 156 (1996),
291-298, doi:10.1016/0012-365X(95)00057-4;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import WantedExt.Complexity.NPComplete.DominatingSetSplitGraphsWanted
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH on strongly chordal split graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is both a split graph (its vertex set can be partitioned
into a clique and an independent set) and strongly chordal (every cycle of length at least `4`
has a chord, and every cycle of even length at least `6` has an odd chord, an edge joining two
vertices of the cycle at odd distance greater than `1` along the cycle).
QUESTION: does `G` contain a Hamiltonian path, that is, a simple path through every vertex
(endpoints not specified)?

Müller (1996, abstract): "The main result of this paper is the NP-completeness of the
HAMILTONIAN CIRCUIT problem for chordal bipartite graphs. [...] As a corollary, HAMILTONIAN
CIRCUIT is NP-complete for strongly chordal split graphs. On both classes the complexity of the
HAMILTONIAN PATH problem coincides with the complexity of HAMILTONIAN CIRCUIT." The ISGCI database
lists HAMILTONIAN PATH as NP-complete on the class "split ∩ strongly chordal" (gc_315), citing
Müller.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted` ([GT39]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian path is an ordering of all vertices in
which consecutive vertices are adjacent). The restriction adds two conjuncts:

* the split-graph predicate `DominatingSetSplitGraphs.IsSplitGraph` of
  `WantedExt.Complexity.NPComplete.DominatingSetSplitGraphsWanted` (a vertex set `C` that is a
  clique, Mathlib's `SimpleGraph.IsClique`, whose complement is independent,
  `SimpleGraph.IsIndepSet`; either part may be empty);
* strong chordality, `IsStronglyChordal`, in the form of Brandstädt, Le and Spinrad, *Graph
  Classes: A Survey* (SIAM, 1999), Definition 3.4.1: chordal, and every even cycle of length at
  least `6` has an odd chord. Chordality is stated as in
  `WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted`: no cycle graph `Cₖ` with
  `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
  `SimpleGraph.IsIndContained`; a cycle has a chord exactly when its vertices do not induce a
  cycle graph). A cycle is a closed walk `c` with Mathlib's `SimpleGraph.Walk.IsCycle`; its
  vertices in order are `c.getVert 0, …, c.getVert (ℓ - 1)` with `ℓ = c.length`, pairwise
  distinct. For positions `i < j < ℓ` the distance along the cycle between `c.getVert i` and
  `c.getVert j` is `min (j - i) (ℓ - (j - i))`; when `ℓ` is even and `j - i` is odd both are odd,
  so this distance is odd and greater than `1` exactly when `j - i` is odd, `3 ≤ j - i` and
  `j - i + 3 ≤ ℓ` (`HasOddChord`). These bounds exclude the cycle's own edges.

Every split graph is chordal, so the chordality conjunct is implied by the split-graph conjunct;
it is kept so that `IsStronglyChordal` is the textbook class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The closed walk `c` (a cycle of length `ℓ`) has an odd chord: positions `i < j < ℓ` with
`j - i` odd, `3 ≤ j - i` and `j - i + 3 ≤ ℓ`, whose vertices are adjacent. -/
def HasOddChord {V : Type*} {G : SimpleGraph V} {v : V} (c : G.Walk v v) : Prop :=
  ∃ i j : ℕ, i < j ∧ j < c.length ∧ Odd (j - i) ∧ 3 ≤ j - i ∧ j - i + 3 ≤ c.length ∧
    G.Adj (c.getVert i) (c.getVert j)

/-- `G` is strongly chordal: it has no induced cycle of length at least `4` (chordal), and every
cycle of even length at least `6` has an odd chord. -/
def IsStronglyChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained G) ∧
    ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length → 6 ≤ c.length → HasOddChord c

/-- Well-formedness of an instance: a well-formed HAMILTONIAN PATH instance whose graph is a
split graph and strongly chordal. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ DominatingSetSplitGraphs.IsSplitGraph (Graph i) ∧
    IsStronglyChordal (Graph i)

open Classical in
/-- HAMILTONIAN PATH on strongly chordal split graphs as a decision problem over bitstrings. -/
noncomputable def stronglyChordalSplitHamiltonianPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on strongly chordal split graphs is NP-complete.** Source: Müller (1996);
Garey and Johnson (1979), [GT39]. -/
public theorem_wanted stronglyChordalSplitHamiltonianPath_npComplete :
    stronglyChordalSplitHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stronglyChordalSplitHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.StronglyChordalSplitHamiltonianPath
