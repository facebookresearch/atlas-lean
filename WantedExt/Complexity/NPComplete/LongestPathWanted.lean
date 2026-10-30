/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), LONGEST PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestPath

/-!
# LONGEST PATH is NP-complete

An undirected graph, a bound `K`, and distinguished endpoints `s` and `t` (Garey-Johnson ND29).
The question is whether the graph has a simple path from `s` to `t` with at least `K` edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A longest-path instance: vertex count, edge list, bound K, start s, target t. -/
abbrev LongestPathInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LongestPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : LongestPathInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.1 < i.1 ∧ i.2.2.2.2 < i.1

/-- A simple path from `s` to `t` with at least `K` edges. -/
def LongestPathFeasible
    (i : LongestPathInstance) : Prop :=
  ∃ path : List (Fin i.1), path.Nodup ∧ i.2.2.1 + 1 ≤ path.length ∧
    (path.head?.map fun v => (v : ℕ)) = some i.2.2.2.1 ∧
    (path.getLast?.map fun v => (v : ℕ)) = some i.2.2.2.2 ∧
    ∀ j (h : j + 1 < path.length),
      (Graph i).Adj (path[j]'(by omega)) (path[j + 1]'h)

open Classical in
/-- LONGEST PATH as a decision problem over bitstrings. -/
noncomputable def longestPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestPathInstance) x with
  | some i => decide (WellFormed i ∧ LongestPathFeasible i)
  | none => false

/-- **LONGEST PATH is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), LONGEST PATH. -/
public theorem_wanted longestPath_npComplete :
    longestPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestPathDec

end MetaMathlibExt.Complexity.NPComplete.LongestPath
