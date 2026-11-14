/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND41] MAXIMUM
LENGTH-BOUNDED DISJOINT PATHS, p. 217 (comment: "Remains NP-complete for all fixed `K ≥ 5`");
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

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK

/-!
# MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with fixed `K ≥ 5` is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, and a positive integer
`J ≤ |V|`; the bound `K ≤ |V|` is a fixed constant, not part of the instance.
QUESTION: does `G` contain `J` or more mutually vertex-disjoint paths from `s` to `t`, none
involving more than `K` edges?

Garey and Johnson state that MAXIMUM LENGTH-BOUNDED DISJOINT PATHS remains NP-complete for
every fixed `K ≥ 5` (and is polynomial for `K ≤ 4`). For each `K` this module defines the
problem with `K` fixed, `maximumLengthBoundedDisjointPathsFixedKDec K`, and states its
NP-completeness for every `K ≥ 5`.

The vertices are `0, ..., n - 1` and the graph is given by a simple edge list; `s` and `t` are
distinct, as in Itai, Perl, and Shiloach ("a graph G with two distinct vertices s and t").
The source's bound `K ≤ |V|` becomes the condition `K ≤ n` on instances. Paths from `s` to
`t` are Mathlib paths `G.Path s t`, and mutual vertex-disjointness is
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

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list, `s`, `t`, `J`. -/
abbrev MaximumLengthBoundedDisjointPathsFixedKInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaximumLengthBoundedDisjointPathsFixedKInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance for the fixed bound `K`: the edge list is simple (endpoints
in range, no self-loops, no repeated or reversed edges), `s` and `t` are distinct vertices,
`0 < J ≤ |V|`, and `K ≤ |V|`. -/
def WellFormed (K : ℕ) (i : MaximumLengthBoundedDisjointPathsFixedKInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
    0 < i.2.2.2.2 ∧ i.2.2.2.2 ≤ i.1 ∧ K ≤ i.1

/-- There are `J` different paths from `s` to `t` in `G`, pairwise sharing no vertex other than
`s` and `t`, each with at most `K` edges. -/
def MaximumLengthBoundedDisjointPathsFixedKFeasible (K : ℕ)
    (i : MaximumLengthBoundedDisjointPathsFixedKInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1)
    (paths : Fin i.2.2.2.2 → (Graph i).Path ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩),
    Function.Injective paths ∧ IsInternallyVertexDisjointSTPaths paths ∧
      ∀ j, (paths j).val.length ≤ K

open Classical in
/-- MAXIMUM LENGTH-BOUNDED DISJOINT PATHS with the fixed bound `K`, as a decision problem over
bitstrings. -/
noncomputable def maximumLengthBoundedDisjointPathsFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLengthBoundedDisjointPathsFixedKInstance) x with
  | some i => decide (WellFormed K i ∧ MaximumLengthBoundedDisjointPathsFixedKFeasible K i)
  | none => false

/-- **MAXIMUM LENGTH-BOUNDED DISJOINT PATHS is NP-complete for every fixed `K ≥ 5`.** Source:
Garey and Johnson (1979), [ND41]; Itai, Perl, and Shiloach (1982). -/
public theorem_wanted maximumLengthBoundedDisjointPathsFixedK_npComplete (K : ℕ) (hK : 5 ≤ K) :
    maximumLengthBoundedDisjointPathsFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (maximumLengthBoundedDisjointPathsFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.MaximumLengthBoundedDisjointPathsFixedK
