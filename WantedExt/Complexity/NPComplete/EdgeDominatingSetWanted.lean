/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), EDGE DOMINATING SET; M.
Yannakakis and F. Gavril, "Edge dominating sets in graphs" (1980).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet

/-!
# EDGE DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` edges
dominates all edges: every edge shares an endpoint with an edge in the set.

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
abbrev EdgeDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- Undirected adjacency from an edge list (as a Bool, for use in filters). -/
def Adj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v) || edges.contains (v, u)


/-- Well-formedness of an instance. -/
def WellFormed (i : EdgeDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- An edge dominating set of at most `K` edges. -/
def EdgeDominatingSetFeasible
    (i : EdgeDominatingSetInstance) : Prop :=
  ∃ D : List (ℕ × ℕ), D.Sublist i.2.1 ∧ D.length ≤ i.2.2 ∧
    ∀ e ∈ i.2.1, ∃ d ∈ D, d.1 = e.1 ∨ d.1 = e.2 ∨ d.2 = e.1 ∨ d.2 = e.2

open Classical in
/-- EDGE DOMINATING SET as a decision problem over bitstrings. -/
noncomputable def edgeDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ EdgeDominatingSetFeasible i)
  | none => false

/-- **EDGE DOMINATING SET is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), EDGE DOMINATING SET; M. Yannakakis and F. Gavril, "Edge
dominating sets in graphs" (1980). -/
public theorem_wanted edgeDominatingSet_npComplete :
    edgeDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L edgeDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.EdgeDominatingSet
