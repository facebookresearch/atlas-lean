/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS;
A. Itai, Y. Perl, and Y. Shiloach, "The complexity of finding maximum disjoint
paths with length constraints", Networks 12 (1982), 277-286,
doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.Graph.MengerVertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths

/-!
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, and positive integers
`J, K ≤ |V|`. QUESTION: does `G` contain `J` or more mutually vertex-disjoint paths from `s` to
`t`, none involving more than `K` edges?

The vertices are `0, ..., n - 1` and the graph is given by a simple edge list; `s` and `t` are
distinct, as in Itai, Perl, and Shiloach ("a graph G with two distinct vertices s and t").
Paths from `s` to `t` are Mathlib paths `G.Path s t`, and mutual vertex-disjointness is
`IsInternallyVertexDisjointSTPaths` from `MathlibExt.Combinatorics.Graph.MengerVertex`: two
distinct paths of the family share no vertex other than `s` and `t`. The family is indexed by
`Fin J` and required to be injective, so it consists of `J` different paths; without that,
the single path along an edge `{s, t}` could be repeated `J` times, since it has no inner
vertex. "`J` or more" paths is the same as `J` paths, because a subfamily of a disjoint family
is disjoint. "Involving no more than `K` edges" is `Walk.length ≤ K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list, `s`, `t`, `J`, `K`. -/
abbrev MaximumLengthBoundedDisjointPathsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaximumLengthBoundedDisjointPathsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list is simple (endpoints in range, no self-loops,
no repeated or reversed edges), `s` and `t` are distinct vertices, and `0 < J ≤ |V|` and
`0 < K ≤ |V|`. -/
def WellFormed (i : MaximumLengthBoundedDisjointPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
    0 < i.2.2.2.2.1 ∧ i.2.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.2 ∧ i.2.2.2.2.2 ≤ i.1

/-- There are `J` different paths from `s` to `t` in `G`, pairwise sharing no vertex other than
`s` and `t`, each with at most `K` edges. -/
def MaximumLengthBoundedDisjointPathsFeasible
    (i : MaximumLengthBoundedDisjointPathsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin i.2.2.2.2.1 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    Function.Injective paths ∧ IsInternallyVertexDisjointSTPaths paths ∧
      ∀ j, (paths j).val.length ≤ i.2.2.2.2.2

open Classical in
/-- MAXIMUM LENGTH-BOUNDED DISJOINT PATHS as a decision problem over bitstrings. -/
noncomputable def maximumLengthBoundedDisjointPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLengthBoundedDisjointPathsInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLengthBoundedDisjointPathsFeasible i)
  | none => false

/-- **MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete.** Source: Garey and Johnson (1979),
[ND41]; Itai, Perl, and Shiloach (1982). -/
public theorem_wanted maximumLengthBoundedDisjointPaths_npComplete :
    maximumLengthBoundedDisjointPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLengthBoundedDisjointPathsDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPaths
