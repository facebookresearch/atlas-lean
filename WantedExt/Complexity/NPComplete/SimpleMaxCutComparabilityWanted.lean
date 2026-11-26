/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on comparability graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, comment ("Remains
NP-complete if `w(e) = 1` for all `e ∈ E` (the SIMPLE MAX CUT problem)"), the problem restricted
here;
R. V. Pocai, "The complexity of SIMPLE MAX-CUT on comparability graphs", Electronic Notes in
Discrete Mathematics 55 (2016), 161-164, doi:10.1016/j.endm.2016.10.040, Theorem 2.3;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutComparability

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on comparability graphs is NP-complete

INSTANCE: a comparability graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that at least `K`
edges of `E` have one endpoint in `V₁` and one endpoint in `V₂`?

This is MAXIMUM CUT with unit weights (SIMPLE MAX CUT, [ND16] comment) restricted to
comparability graphs. Pocai (2016, Theorem 2.3) proves SIMPLE MAX-CUT NP-hard on comparability
graphs, by a reduction from SET SPLITTING adapted from Masuda et al.'s proof for FIXED LINEAR
CROSSING NUMBER; de Figueiredo, de Melo, Sasaki and Silva (2022) record the entry, which
Johnson's 1985 table had left open. Membership in NP: the certificate is the partition together
with a transitive orientation of `G`, both checkable in polynomial time.

The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`WantedExt.Complexity.NPComplete.MaxCutWanted`, whose question already counts edges), reused
here as in `SimpleMaxCutDegreeThreeWanted`. The restriction is the comparability-graph predicate
`ComparabilityGraphSandwich.IsComparabilityGraph` from
`WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted` (some strict partial order `r`
on the vertices, Mathlib's `IsStrictOrder`, makes two vertices adjacent exactly when they are
comparable under `r`; Pocai's definition: "u, v ∈ V are adjacent if and only if u ≺ v or
v ≺ u") applied to `Cslib.Complexity.Karp.edgeGraph`, plus `0 < K` as in [ND16].

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n`, the edge list, and the bound `K`; this is the MAXIMUM
CUT instance type. -/
abbrev SimpleMaxCutComparabilityInstance := MaxCutInstance

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is a comparability graph, and `0 < K`. -/
def WellFormed (i : SimpleMaxCutComparabilityInstance) : Prop :=
  MaxCut.WellFormed i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` with at least `K` edges between the two sets (the
MAXIMUM CUT question). -/
def SimpleMaxCutComparabilityFeasible (i : SimpleMaxCutComparabilityInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on comparability graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutComparabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SimpleMaxCutComparabilityInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutComparabilityFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on comparability graphs is NP-complete.** Source: Pocai (2016),
Theorem 2.3; Garey and Johnson (1979), [ND16]. -/
public theorem_wanted simpleMaxCutComparability_npComplete :
    simpleMaxCutComparabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutComparabilityDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutComparability
