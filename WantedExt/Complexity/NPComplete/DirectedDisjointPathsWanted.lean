/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED DISJOINT PATHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), DISJOINT PATHS; S.
Fortune, J. Hopcroft, and J. Wyllie, "The directed subgraph homeomorphism problem" (1980).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedDisjointPaths

/-!
# DIRECTED DISJOINT PATHS is NP-complete

A directed graph and a list of source-target pairs. The question is whether there are pairwise
vertex-disjoint directed paths joining each pair, with paths simple and endpoints matching the
pairs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A directed-disjoint-paths instance: vertex count, arc list, source-target pairs. -/
abbrev DirectedDisjointPathsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)


/-- Directed adjacency from an edge list (as a Bool, for use in filters). -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- Well-formedness of an instance. -/
def WellFormed (i : DirectedDisjointPathsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (∀ p ∈ i.2.2, p.1 < i.1 ∧ p.2 < i.1)

/-- Pairwise vertex-disjoint directed paths for all pairs. -/
def DirectedDisjointPathsFeasible
    (i : DirectedDisjointPathsInstance) : Prop :=
  ∃ paths : List (List ℕ), paths.length = i.2.2.length ∧
    (∀ p < i.2.2.length, (paths.getD p []).Nodup ∧ (paths.getD p []).length ≥ 1 ∧
      (paths.getD p []).getD 0 0 = (i.2.2.getD p (0, 0)).1 ∧
      (paths.getD p []).getD ((paths.getD p []).length - 1) 0 = (i.2.2.getD p (0, 0)).2 ∧
      (∀ v ∈ paths.getD p [], v < i.1) ∧
      ∀ j, j + 1 < (paths.getD p []).length →
        DAdj i.2.1 ((paths.getD p []).getD j 0) ((paths.getD p []).getD (j + 1) 0)) ∧
    ∀ p < i.2.2.length, ∀ q < i.2.2.length, p ≠ q → ∀ v < i.1,
      v ∈ paths.getD p [] → v ∉ paths.getD q []

open Classical in
/-- DIRECTED DISJOINT PATHS as a decision problem over bitstrings. -/
noncomputable def directedDisjointPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedDisjointPathsInstance) x with
  | some i => decide (WellFormed i ∧ DirectedDisjointPathsFeasible i)
  | none => false

/-- **DIRECTED DISJOINT PATHS is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), DISJOINT PATHS; S. Fortune, J. Hopcroft, and J.
Wyllie, "The directed subgraph homeomorphism problem" (1980). -/
public theorem_wanted directedDisjointPaths_npComplete :
    directedDisjointPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedDisjointPathsDec

end MetaMathlibExt.Complexity.NPComplete.DirectedDisjointPaths
