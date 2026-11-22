/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARABILITY GRAPH SANDWICH is NP-complete

Source:
M. C. Golumbic, H. Kaplan and R. Shamir, "Graph sandwich problems", Journal of Algorithms 19(3)
(1995), 449-473, doi:10.1006/jagm.1995.1047.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IntervalGraphSandwichWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphSandwich

/-!
# COMPARABILITY GRAPH SANDWICH is NP-complete

INSTANCE: graphs `G₁ = (V, E₁)` and `G₂ = (V, E₂)` on the same vertex set with `E₁ ⊆ E₂`.
QUESTION: is there a comparability graph `G = (V, E)` with `E₁ ⊆ E ⊆ E₂`?

A comparability graph is a graph that has a transitive orientation, i.e. the comparability
graph of a partial order: there is a strict partial order `r` on `V` (Mathlib's
`IsStrictOrder`) such that two vertices are adjacent exactly when they are comparable under
`r`. The instance, the graphs `G₁` (required edges) and `G₂` (allowed edges) and the
well-formedness condition are those of INTERVAL GRAPH SANDWICH
(`WantedExt.Complexity.NPComplete.IntervalGraphSandwichWanted`:
`IntervalGraphSandwich.IntervalGraphSandwichInstance`, `IntervalGraphSandwich.Lower`,
`IntervalGraphSandwich.Upper`, `IntervalGraphSandwich.WellFormed`); the sandwich graph `G` is a
`SimpleGraph` `H` on the same vertices with `G₁ ≤ H ≤ G₂`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `H` is a comparability graph: some strict partial order `r` on the vertices makes two
vertices adjacent exactly when they are comparable (`r` orients each edge transitively). -/
def IsComparabilityGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ r : V → V → Prop, IsStrictOrder V r ∧ ∀ u v, H.Adj u v ↔ r u v ∨ r v u

/-- Some comparability graph `H` on the same vertices contains every required edge and only
allowed edges. -/
def ComparabilityGraphSandwichFeasible
    (i : IntervalGraphSandwich.IntervalGraphSandwichInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), IntervalGraphSandwich.Lower i ≤ H ∧
    H ≤ IntervalGraphSandwich.Upper i ∧ IsComparabilityGraph H

open Classical in
/-- COMPARABILITY GRAPH SANDWICH as a decision problem over bitstrings. -/
noncomputable def comparabilityGraphSandwichDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphSandwich.IntervalGraphSandwichInstance) x with
  | some i => decide (IntervalGraphSandwich.WellFormed i ∧ ComparabilityGraphSandwichFeasible i)
  | none => false

/-- **COMPARABILITY GRAPH SANDWICH is NP-complete.** Source: Golumbic, Kaplan and Shamir
(1995). -/
public theorem_wanted comparabilityGraphSandwich_npComplete :
    comparabilityGraphSandwichDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L comparabilityGraphSandwichDec

end MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphSandwich
