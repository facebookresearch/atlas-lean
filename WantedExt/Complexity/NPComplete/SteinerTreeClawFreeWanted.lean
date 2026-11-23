/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for claw-free graphs is NP-complete

Source:
H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van Leeuwen,
"Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical Computer
Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (arXiv:2004.07492), Lemma 8 ("The
unweighted Vertex Steiner Tree problem is NP-complete for line graphs") and the proof of
Theorem 2 ("the class of claw-free graphs, which in turn contains the class of line graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the
parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SteinerTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeClawFree

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-!
# STEINER TREE IN GRAPHS (unit weights) for claw-free graphs is NP-complete

INSTANCE: a claw-free graph `G = (V, E)` (no induced `K₁,₃`), a set `R ⊆ V` of terminals and a
positive integer `K`. QUESTION: is there a subtree of `G` containing every vertex of `R` and
having at most `K` edges?

This is STEINER TREE IN GRAPHS ([ND12], `SteinerTreeWanted`) with unit edge weights, restricted
to claw-free graphs. Bodlaender, Brettell, Johnson, Paesani, Paulusma and van Leeuwen prove the
unweighted problem NP-complete for line graphs (their Lemma 8, with the Steiner-vertex count as
the bound; in a tree the number of edges is the number of vertices minus one, so the two bounds
are interchangeable), and line graphs are claw-free. The instance (vertex count, weighted edge
list, terminals, budget), the parent's well-formedness and the question (a sub-list of the edges
of total weight at most `K` connecting all terminals; a minimal such edge set is a tree) are the
parent's, as in `SteinerTreeSplitGraphsWanted`; the restriction adds to `WellFormed` that every
edge has weight `1`, that the graph `SteinerTree.Graph i i.2.1` is claw-free, and `0 < K` (the
source's "positive integer").

Claw-freeness is the repository's predicate `SimpleGraph.IsClawFree` (from
`MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly`, as in `PolarityClawFreeWanted`):
no vertex `c` with three distinct, pairwise non-adjacent neighbours `l₁, l₂, l₃`, i.e. no induced
`K₁,₃`.

Membership in NP holds for STEINER TREE IN GRAPHS, and claw-freeness is checked in `O(n⁴)` time;
vertices outside the edge list are isolated and change neither the class nor the answer (an
isolated terminal makes the instance a no-instance unless it is the only terminal), so the binary
vertex count does not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed STEINER TREE IN GRAPHS instance in which every
edge has weight `1`, whose graph is claw-free, and `0 < K`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).IsClawFree ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for claw-free graphs as a decision problem
over bitstrings. -/
noncomputable def steinerTreeClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

/-- **STEINER TREE IN GRAPHS (unit weights) for claw-free graphs is NP-complete.**
Source: Bodlaender, Brettell, Johnson, Paesani, Paulusma and van Leeuwen (2021), Lemma 8. -/
public theorem_wanted steinerTreeClawFree_npComplete :
    steinerTreeClawFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L steinerTreeClawFreeDec

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeClawFree
