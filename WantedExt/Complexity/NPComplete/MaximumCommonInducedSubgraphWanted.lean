/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM COMMON INDUCED
SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph

/-!
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Two undirected graphs and a bound `K`. The question is whether they have a common induced
subgraph on at least `K` vertices: subsets of vertices of the two graphs and a bijection
between them preserving adjacency in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A maximum-common-induced-subgraph instance: first vertex count, first edges, second vertex
count, second edges, bound. -/
abbrev MaximumCommonInducedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ


/-- The first graph. -/
def GraphFirst (i : MaximumCommonInducedSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The second graph. -/
def GraphSecond (i : MaximumCommonInducedSubgraphInstance) :
    SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2.1


/-- Well-formedness of an instance. -/
def WellFormed (i : MaximumCommonInducedSubgraphInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.1.Nodup ∧
    ∀ e ∈ i.2.2.2.1, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1

/-- A common induced subgraph on at least `K` vertices. -/
def MaximumCommonInducedSubgraphFeasible
    (i : MaximumCommonInducedSubgraphInstance) : Prop :=
  ∃ A : Finset (Fin i.1), ∃ B : Finset (Fin i.2.2.1),
    i.2.2.2.2 ≤ A.card ∧ B.card = A.card ∧
    ∃ f : ↥A → ↥B, Function.Bijective f ∧
      ∀ a b : ↥A,
        (GraphFirst i).Adj (a : Fin i.1) (b : Fin i.1) ↔
          (GraphSecond i).Adj (f a : Fin i.2.2.1) (f b : Fin i.2.2.1)

open Classical in
/-- MAXIMUM COMMON INDUCED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def maximumCommonInducedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumCommonInducedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ MaximumCommonInducedSubgraphFeasible i)
  | none => false

/-- **MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MAXIMUM COMMON INDUCED SUBGRAPH. -/
public theorem_wanted maximumCommonInducedSubgraph_npComplete :
    maximumCommonInducedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCommonInducedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph
