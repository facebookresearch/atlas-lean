/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ODD CYCLE TRANSVERSAL is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL
(vertex deletion to a bipartite graph).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal

/-!
# ODD CYCLE TRANSVERSAL is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` vertices can be
removed to make the graph bipartite, witnessed by a two-coloring of the remaining vertices.

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
abbrev OddCycleTransversalInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : OddCycleTransversalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : OddCycleTransversalInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- At most `K` vertices whose removal leaves a bipartite graph. -/
def OddCycleTransversalFeasible
    (i : OddCycleTransversalInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ((Graph i).induce (↑Sᶜ : Set (Fin i.1))).IsBipartite

open Classical in
/-- ODD CYCLE TRANSVERSAL as a decision problem over bitstrings. -/
noncomputable def oddCycleTransversalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OddCycleTransversalInstance) x with
  | some i => decide (WellFormed i ∧ OddCycleTransversalFeasible i)
  | none => false

/-- **ODD CYCLE TRANSVERSAL is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), ODD CYCLE TRANSVERSAL (vertex deletion to a
bipartite graph). -/
public theorem_wanted oddCycleTransversal_npComplete :
    oddCycleTransversalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L oddCycleTransversalDec

end MetaMathlibExt.Complexity.NPComplete.OddCycleTransversal
