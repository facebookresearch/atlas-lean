/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on triangle-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET;
S. Poljak, "A note on stable sets and colorings of graphs", Commentationes
Mathematicae Universitatis Carolinae 15 (1974), 307-309.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TriangleFreeIndependentSet

/-!
# INDEPENDENT SET on triangle-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that contains no triangle, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

Poljak's construction gives the reduction from INDEPENDENT SET: replacing every edge of a graph
with `m` edges by a path of three edges yields a triangle-free graph whose independence number
is larger by exactly `m`. INDEPENDENT SET itself is proved NP-complete in
`CSLibExt.Computability.Complexity.Karp` (`Cslib.Complexity.Karp.indSetDec`, with its own
adjacency-bit encoding); this module states the restriction to triangle-free graphs with the
edge-list encoding of the statements in this directory.

"No triangle" is Mathlib's `SimpleGraph.CliqueFree 3`; the independent set is a `Finset` whose
coercion is `SimpleGraph.IsIndepSet`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev TriangleFreeIndependentSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TriangleFreeIndependentSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that contains no
triangle, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).CliqueFree 3 ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at least `K` vertices contains no two adjacent vertices. -/
def TriangleFreeIndependentSetFeasible (i : TriangleFreeIndependentSetInstance) : Prop :=
  ∃ s : Finset (Fin i.1), i.2.2 ≤ s.card ∧ (Graph i).IsIndepSet (s : Set (Fin i.1))

open Classical in
/-- INDEPENDENT SET on triangle-free graphs as a decision problem over bitstrings. -/
noncomputable def triangleFreeIndependentSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET is NP-complete on triangle-free graphs.** Source: Garey and Johnson
(1979), [GT20]; Poljak (1974). -/
public theorem_wanted triangleFreeIndependentSet_npComplete :
    triangleFreeIndependentSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L triangleFreeIndependentSetDec

end MetaMathlibExt.Complexity.NPComplete.TriangleFreeIndependentSet
