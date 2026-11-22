/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE COLORING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE COLORING; I. Holyer,
"The NP-completeness of edge-coloring" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeColoring

/-!
# EDGE COLORING is NP-complete

An undirected graph and a bound `K`. The question is whether the chromatic index is at most
`K`: a coloring of the edges with colors `0, …, K - 1` in which edges sharing an endpoint
differ.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev EdgeColoringInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- Undirected adjacency from an edge list (as a Bool, for use in filters). -/
def Adj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v) || edges.contains (v, u)


/-- Well-formedness of an instance. -/
def WellFormed (i : EdgeColoringInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A proper edge coloring with at most `K` colors. -/
def EdgeColoringFeasible
    (i : EdgeColoringInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.2.1.length ∧ (∀ c ∈ coloring, c < i.2.2) ∧
    ∀ a < i.2.1.length, ∀ b < i.2.1.length, a ≠ b →
      ((i.2.1.getD a (0, 0)).1 = (i.2.1.getD b (0, 0)).1 ∨
        (i.2.1.getD a (0, 0)).1 = (i.2.1.getD b (0, 0)).2 ∨
        (i.2.1.getD a (0, 0)).2 = (i.2.1.getD b (0, 0)).1 ∨
        (i.2.1.getD a (0, 0)).2 = (i.2.1.getD b (0, 0)).2) →
      coloring.getD a 0 ≠ coloring.getD b 0

open Classical in
/-- EDGE COLORING as a decision problem over bitstrings. -/
noncomputable def edgeColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ EdgeColoringFeasible i)
  | none => false

/-- **EDGE COLORING is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), EDGE COLORING; I. Holyer, "The NP-completeness of edge-coloring"
(1981). -/
public theorem_wanted edgeColoring_npComplete :
    edgeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeColoringDec

end MetaMathlibExt.Complexity.NPComplete.EdgeColoring
