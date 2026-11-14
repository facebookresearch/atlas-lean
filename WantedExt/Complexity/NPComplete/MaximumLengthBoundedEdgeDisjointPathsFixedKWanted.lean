/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 217, problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, comment: "Problem where paths need only be edge-disjoint is
NP-complete for all fixed `K ≥ 5`";
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.MengerEdge
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedK

open MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths
open MathlibExt.Combinatorics.SimpleGraph.MengerEdgeWanted

/-!
# MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

For a fixed constant `K ≥ 5`: given a graph `G = (V, E)`, specified vertices `s` and `t`, and a
positive integer `J ≤ |V|`, does `G` contain `J` or more mutually edge-disjoint paths from `s`
to `t`, none involving more than `K` edges?

This is the edge-disjoint version of MAXIMUM LENGTH-BOUNDED DISJOINT PATHS
(`WantedExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsWanted`), with `K` no longer
part of the instance. The instance is the graph, `s`, `t` and `J`, and `withBound i K` appends
the fixed `K` to obtain an instance of that problem, whose `Graph` and `WellFormed` (simple edge
list, `s ≠ t`, and the source's `0 < J ≤ |V|`, `0 < K ≤ |V|`) are reused unchanged. Only the
question changes: mutual edge-disjointness is `IsEdgeDisjointSTPaths` from
`MathlibExt.Combinatorics.SimpleGraph.MengerEdge` (two distinct paths of the family share no
edge). Since `s ≠ t`, every path from `s` to `t` has an edge, so an edge-disjoint family of `J`
paths consists of `J` different paths, and "`J` or more" paths is the same as `J` paths.
"Involving no more than `K` edges" is `Walk.length ≤ K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance for a fixed bound: vertex count `n` (vertices `0, ..., n - 1`), edge list,
`s`, `t`, `J`. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The MAXIMUM LENGTH-BOUNDED DISJOINT PATHS instance given by `i` and the bound `K`. -/
abbrev withBound (i : FixedBoundInstance) (K : ℕ) : MaximumLengthBoundedDisjointPathsInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2, K)

/-- There are `J` paths from `s` to `t` in `G`, pairwise sharing no edge, each with at most `K`
edges. -/
def EdgeDisjointFeasible (i : MaximumLengthBoundedDisjointPathsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin i.2.2.2.2.1 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    IsEdgeDisjointSTPaths paths ∧ ∀ j, (paths j).val.length ≤ i.2.2.2.2.2

open Classical in
/-- MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS with the bound fixed to `K`, as a decision
problem over bitstrings. -/
noncomputable def fixedBoundDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed (withBound i K) ∧ EdgeDisjointFeasible (withBound i K))
  | none => false

/-- **MAXIMUM LENGTH-BOUNDED EDGE-DISJOINT PATHS is NP-complete for every fixed `K ≥ 5`.**
Source: Garey and Johnson (1979), [ND41], comment; Itai, Perl, and Shiloach (1982). -/
public theorem_wanted maximumLengthBoundedEdgeDisjointPathsFixedK_npComplete (K : ℕ)
    (hK : 5 ≤ K) :
    fixedBoundDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (fixedBoundDec K)

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedEdgeDisjointPathsFixedK
