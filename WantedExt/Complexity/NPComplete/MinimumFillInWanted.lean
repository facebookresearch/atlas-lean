/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M.
Yannakakis, "Computing the minimum fill-in is NP-complete" (1981).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumFillIn

/-!
# MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete

An undirected graph and a bound `K`. The question is whether at most `K` edges can be added so
that the resulting graph is chordal, witnessed by a perfect elimination ordering: a vertex
ordering in which, for every vertex, its later neighbors form a clique in the augmented graph.

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
abbrev MinimumFillInInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- The graph augmented by added edges. -/
def GraphAug (i : MinimumFillInInstance) (added : List (ℕ × ℕ)) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1 ++ added)


/-- Well-formedness of an instance. -/
def WellFormed (i : MinimumFillInInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- At most `K` added edges making the graph chordal. -/
def MinimumFillInFeasible
    (i : MinimumFillInInstance) : Prop :=
  ∃ ord : List (Fin i.1), ord.Perm (List.finRange i.1) ∧
    ∃ added : List (ℕ × ℕ), added.Nodup ∧ added.length ≤ i.2.2 ∧
      (∀ e ∈ added, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ added ∧
        (e.2, e.1) ∉ i.2.1 ∧ e ∉ i.2.1) ∧
      ∀ v a b : Fin i.1, a ≠ b → ord.idxOf v < ord.idxOf a →
        ord.idxOf v < ord.idxOf b → (GraphAug i added).Adj v a →
        (GraphAug i added).Adj v b → (GraphAug i added).Adj a b

open Classical in
/-- MINIMUM FILL-IN (CHORDAL COMPLETION) as a decision problem over bitstrings. -/
noncomputable def minimumFillInDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumFillInInstance) x with
  | some i => decide (WellFormed i ∧ MinimumFillInFeasible i)
  | none => false

/-- **MINIMUM FILL-IN (CHORDAL COMPLETION) is NP-complete.** Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), MINIMUM FILL-IN; M. Yannakakis, "Computing
the minimum fill-in is NP-complete" (1981). -/
public theorem_wanted minimumFillIn_npComplete :
    minimumFillInDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumFillInDec

end MetaMathlibExt.Complexity.NPComplete.MinimumFillIn
