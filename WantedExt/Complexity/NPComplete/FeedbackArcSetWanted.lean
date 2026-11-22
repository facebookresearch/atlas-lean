/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK ARC SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), FEEDBACK ARC SET; R. M.
Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet

/-!
# FEEDBACK ARC SET is NP-complete

A directed graph and a bound `K`. The question is whether at most `K` arcs can be removed to
make the digraph acyclic, equivalently whether some vertex ordering has at most `K` backward
arcs.

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
abbrev FeedbackArcSetInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- Directed adjacency from an edge list (as a Bool, for use in filters). -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)


/-- Well-formedness of an instance. -/
def WellFormed (i : FeedbackArcSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- A vertex ordering with at most `K` backward arcs. -/
def FeedbackArcSetFeasible
    (i : FeedbackArcSetInstance) : Prop :=
  ∃ ord : List ℕ, ord.Perm (List.range i.1) ∧
    (i.2.1.filter (fun e => decide (ord.idxOf e.2 < ord.idxOf e.1))).length ≤ i.2.2

open Classical in
/-- FEEDBACK ARC SET as a decision problem over bitstrings. -/
noncomputable def feedbackArcSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackArcSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackArcSetFeasible i)
  | none => false

/-- **FEEDBACK ARC SET is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), FEEDBACK ARC SET; R. M. Karp, "Reducibility among combinatorial
problems" (1972). -/
public theorem_wanted feedbackArcSet_npComplete :
    feedbackArcSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackArcSetDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackArcSet
