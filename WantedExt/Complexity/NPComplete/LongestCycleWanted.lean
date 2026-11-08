/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST CYCLE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST CYCLE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCycle

/-!
# LONGEST CYCLE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a simple cycle with
at least `K` edges (and at least three vertices).

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
abbrev LongestCycleInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LongestCycleInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : LongestCycleInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A simple cycle with at least `K` edges. -/
def LongestCycleFeasible
    (i : LongestCycleInstance) : Prop :=
  ∃ cycle : List (Fin i.1), cycle.Nodup ∧ i.2.2 ≤ cycle.length ∧ 3 ≤ cycle.length ∧
    (∀ j (h : j + 1 < cycle.length),
      (Graph i).Adj (cycle[j]'(by omega)) (cycle[j + 1]'h)) ∧
    ∀ h : cycle ≠ [], (Graph i).Adj (cycle.getLast h) (cycle.head h)

open Classical in
/-- LONGEST CYCLE as a decision problem over bitstrings. -/
noncomputable def longestCycleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestCycleInstance) x with
  | some i => decide (WellFormed i ∧ LongestCycleFeasible i)
  | none => false

/-- **LONGEST CYCLE is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST CYCLE. -/
public theorem_wanted longestCycle_npComplete :
    longestCycleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCycleDec

end MetaMathlibExt.Complexity.NPComplete.LongestCycle
