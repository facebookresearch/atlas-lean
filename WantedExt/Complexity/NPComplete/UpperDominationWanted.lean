/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPPER DOMINATION is NP-complete

Source:
G. A. Cheston, G. Fricke, S. T. Hedetniemi and D. P. Jacobs, "On the computational complexity of
upper fractional domination", Discrete Applied Mathematics 27(3) (1990), 195-207,
doi:10.1016/0166-218X(90)90065-K.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpperDomination

open MetaMathlibExt.Complexity.NPComplete.DominatingSet (DominatingSetInstance Graph)

/-!
# UPPER DOMINATION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.

QUESTION: does `G` have a minimal dominating set of size at least `K`, that is, a set `V' ⊆ V`
with `|V'| ≥ K` such that every vertex outside `V'` has a neighbor in `V'` and no proper subset
of `V'` has this property? Equivalently, is the upper domination number `Γ(G)` at least `K`?

Cheston, Fricke, Hedetniemi and Jacobs (1990, abstract) study "`Γ(G)`, the maximum cardinality
of a minimal dominating set in a graph `G = (V, E)`" and show that "the decision problems
corresponding to the problems of computing `Γ(G)` and `Γ_f(G)` are NP-complete". Membership in
NP: `V'` is a certificate; it is dominating, and it is minimal exactly when `V' - {v}` is not
dominating for every `v ∈ V'` (domination is preserved by supersets), which is checked in
polynomial time. `K ≤ |V|` follows the convention of Garey and Johnson: for `K > |V|` the answer
is trivially no.

The instance, the graph and the simple-graph condition are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: `DominatingSet.DominatingSetInstance`,
a vertex count `n`, vertices `Fin n`, an edge list and the bound `K`; `DominatingSet.Graph`;
`DominatingSet.WellFormed`); only the question differs. Domination is `SimpleGraph.IsDominating` of
`MathlibExt.Combinatorics.SimpleGraph.Domination`, and minimality is Mathlib's `Minimal`
(inclusion-minimal among dominating vertex sets).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`DominatingSet.WellFormed`), and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some minimal dominating set has at least `K` vertices. -/
def UpperDominationFeasible (i : DominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ Minimal (Graph i).IsDominating (S : Set (Fin i.1))

open Classical in
/-- UPPER DOMINATION as a decision problem over bitstrings. -/
noncomputable def upperDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ UpperDominationFeasible i)
  | none => false

/-- **UPPER DOMINATION is NP-complete.** Source: Cheston, Fricke, Hedetniemi and Jacobs
(1990). -/
public theorem_wanted upperDomination_npComplete :
    upperDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L upperDominationDec

end MetaMathlibExt.Complexity.NPComplete.UpperDomination
