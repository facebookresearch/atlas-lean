/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED PATH COVER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), PATH COVER (the `K = 1`
slice is Hamiltonian path).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedPathCover

/-!
# DIRECTED PATH COVER is NP-complete

A directed graph and a bound `K`. The question is whether all vertices can be covered by at
most `K` directed paths: simple vertex-disjoint paths (singleton paths allowed) whose vertex
sets partition the vertex set.

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
abbrev DirectedPathCoverInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- Directed adjacency from an edge list (as a Bool, for use in filters). -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- Well-formedness of an instance. -/
def WellFormed (i : DirectedPathCoverInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- A cover of all vertices by at most `K` directed paths. -/
def DirectedPathCoverFeasible
    (i : DirectedPathCoverInstance) : Prop :=
  ∃ paths : List (List ℕ), paths.length ≤ i.2.2 ∧
    (∀ p ∈ paths, p.Nodup ∧ (∀ v ∈ p, v < i.1) ∧
      ∀ j, j + 1 < p.length → DAdj i.2.1 (p.getD j 0) (p.getD (j + 1) 0)) ∧
    ∀ v < i.1, ∃ p ∈ paths, v ∈ p ∧ ∀ p' ∈ paths, v ∈ p' → p' = p

open Classical in
/-- DIRECTED PATH COVER as a decision problem over bitstrings. -/
noncomputable def directedPathCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedPathCoverInstance) x with
  | some i => decide (WellFormed i ∧ DirectedPathCoverFeasible i)
  | none => false

/-- **DIRECTED PATH COVER is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), PATH COVER (the `K = 1` slice is Hamiltonian path). -/
public theorem_wanted directedPathCover_npComplete :
    directedPathCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedPathCoverDec

end MetaMathlibExt.Complexity.NPComplete.DirectedPathCover
