/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM FIXED-LENGTH DISJOINT PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND42] MAXIMUM FIXED-LENGTH
DISJOINT PATHS;
A. Itai, Y. Perl and Y. Shiloach, "The complexity of finding maximum disjoint paths with
length constraints", Networks 12 (1982), 277-286, doi:10.1002/net.3230120306.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Connectivity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths

/-!
# MAXIMUM FIXED-LENGTH DISJOINT PATHS is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, and positive integers
`J, K ≤ |V|`. QUESTION: does `G` contain `J` or more mutually vertex-disjoint paths from `s` to
`t`, each involving exactly `K` edges?

Paths from `s` to `t` are Mathlib `SimpleGraph.Walk`s with `SimpleGraph.Walk.IsPath`, and
"involving exactly `K` edges" is `SimpleGraph.Walk.length = K`. "Mutually vertex-disjoint"
paths between the same two vertices share only their endpoints `s` and `t`; this is MathlibExt's
`SimpleGraph.InternallyDisjoint`, required for every pair of distinct paths. The paths are also
required to be distinct (`Function.Injective`): two copies of the single edge `{s, t}` share no
inner vertex, but they are one path. `J` or more such paths exist iff `J` of them do, so the
family is indexed by `Fin J`. Itai, Perl and Shiloach take `s` and `t` distinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list, the vertices `s` and `t`,
the number of paths `J`, and the path length `K`. -/
abbrev MaximumFixedLengthDisjointPathsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaximumFixedLengthDisjointPathsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), `s` and `t` are
distinct vertices, and `0 < J ≤ n` and `0 < K ≤ n`. -/
def WellFormed (i : MaximumFixedLengthDisjointPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧
    0 < i.2.2.2.2.1 ∧ i.2.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2.2 ∧ i.2.2.2.2.2 ≤ i.1

/-- There are `J` distinct paths from `s` to `t`, each with exactly `K` edges, such that any two
of them share no vertex other than `s` and `t`. -/
def MaximumFixedLengthDisjointPathsFeasible (i : MaximumFixedLengthDisjointPathsInstance) :
    Prop :=
  ∃ hs : i.2.2.1 < i.1, ∃ ht : i.2.2.2.1 < i.1,
    ∃ P : Fin i.2.2.2.2.1 → (Graph i).Walk ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩,
      Function.Injective P ∧ (∀ k, (P k).IsPath ∧ (P k).length = i.2.2.2.2.2) ∧
        Pairwise fun a b => SimpleGraph.InternallyDisjoint (P a) (P b)

open Classical in
/-- MAXIMUM FIXED-LENGTH DISJOINT PATHS as a decision problem over bitstrings. -/
noncomputable def maximumFixedLengthDisjointPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumFixedLengthDisjointPathsInstance) x with
  | some i => decide (WellFormed i ∧ MaximumFixedLengthDisjointPathsFeasible i)
  | none => false

/-- **MAXIMUM FIXED-LENGTH DISJOINT PATHS is NP-complete.** Source: Garey and Johnson (1979),
[ND42]; Itai, Perl and Shiloach (1982). -/
public theorem_wanted maximumFixedLengthDisjointPaths_npComplete :
    maximumFixedLengthDisjointPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumFixedLengthDisjointPathsDec

end MetaMathlibExt.Complexity.NPComplete.MaximumFixedLengthDisjointPaths
