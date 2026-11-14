/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH SQUARE ROOT is NP-complete

Source:
R. Motwani and M. Sudan, "Computing roots of graphs is hard", Discrete Applied Mathematics 54
(1994), 81-88, doi:10.1016/0166-218X(94)00023-9;
recorded in B. Farzad and M. Karimi, "Square-root finding problem in graphs, a complete dichotomy
theorem", arXiv:1210.7684 (2012), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Square

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot

/-!
# GRAPH SQUARE ROOT is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected). QUESTION: is there a graph `H` on the
same vertex set `V` with `H² = G`, that is, distinct `u` and `v` are adjacent in `G` exactly when
their distance in `H` is at most `2`?

Motwani and Sudan prove that deciding whether a graph has a square root is NP-complete; Farzad
and Karimi (Section 1) record it: "Motwani and Sudan proved that it is NP-complete to determine if
a given graph G is the square of some graph".

The graph is given by its vertex count and a simple edge list (`Cslib.Complexity.Karp.edgeGraph`).
The square is MathlibExt's `SimpleGraph.square`: distinct vertices are adjacent when they are
adjacent in `H` or have a common neighbor in `H`, i.e. when their distance in `H` is `1` or `2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` and edge list. -/
abbrev GraphSquareRootInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GraphSquareRootInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : GraphSquareRootInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- Some graph `H` on the same vertices has square `G`. -/
def GraphSquareRootFeasible (i : GraphSquareRootInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H.square = Graph i

open Classical in
/-- GRAPH SQUARE ROOT as a decision problem over bitstrings. -/
noncomputable def graphSquareRootDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphSquareRootInstance) x with
  | some i => decide (WellFormed i ∧ GraphSquareRootFeasible i)
  | none => false

/-- **GRAPH SQUARE ROOT is NP-complete.** Source: Motwani and Sudan (1994). -/
public theorem_wanted graphSquareRoot_npComplete :
    graphSquareRootDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphSquareRootDec

end MetaMathlibExt.Complexity.NPComplete.GraphSquareRoot
