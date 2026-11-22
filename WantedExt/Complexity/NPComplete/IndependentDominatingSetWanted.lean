/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDEPENDENT DOMINATING
SET (a small maximal independent set).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

/-!
# INDEPENDENT DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set of at most `K` vertices
is both independent (no edge inside the set) and dominating.

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
abbrev IndependentDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : IndependentDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- An independent dominating set of at most `K` vertices. -/
def IndependentDominatingSetFeasible
    (i : IndependentDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    (∀ v : Fin i.1, v ∈ S ∨ ∃ u ∈ S, (Graph i).Adj u v) ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ (Graph i).Adj u v

open Classical in
/-- INDEPENDENT DOMINATING SET as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSetFeasible i)
  | none => false

/-- **INDEPENDENT DOMINATING SET is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), INDEPENDENT DOMINATING SET (a small maximal
independent set). -/
public theorem_wanted independentDominatingSet_npComplete :
    independentDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet
