/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of k-regular comparability graphs (fixed k ≥ 3) is NP-complete

Source:
L. Cai and J. A. Ellis, "NP-completeness of edge-colouring some restricted graphs", Discrete
Applied Mathematics 30(1) (1991), 15-27, doi:10.1016/0166-218X(91)90010-T;
restated in E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying k-Edge Colouring for
H-free graphs", Information Processing Letters 146 (2019), 39-43,
doi:10.1016/j.ipl.2019.02.006 (arXiv:1810.04379), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ChromaticIndexRegularWanted
public import WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegularComparability

open MetaMathlibExt.Complexity.NPComplete

/-!
# CHROMATIC INDEX of k-regular comparability graphs (fixed k ≥ 3) is NP-complete

Fix an integer `k ≥ 3`. An instance is a `k`-regular comparability graph `G = (V, E)`. The
question is whether the edges of `G` can be colored with `k` colors so that edges sharing an
endpoint get different colors. Cai and Ellis (1991) proved this NP-complete; Galby, Lima,
Paulusma and Ries (2019) restate it: "Cai and Ellis proved that for every `k ≥ 3`, `k`-Edge
Colouring is NP-complete for `k`-regular comparability graphs."

This is CHROMATIC INDEX of `k`-regular graphs
(`MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegular`) restricted to comparability
graphs. The instance type, the graph, the well-formedness conditions (simple edge list,
`k`-regular) and the question are that module's; this module adds only the comparability
condition to `WellFormed`.

A comparability graph is a graph whose edges are exactly the comparable pairs of some partial
order on its vertices: `ComparabilityGraphSandwich.IsComparabilityGraph` (from COMPARABILITY
GRAPH SANDWICH, `WantedExt.Complexity.NPComplete.ComparabilityGraphSandwichWanted`), stated with
a strict partial order `r` (Mathlib's `IsStrictOrder`): `u` and `v` are adjacent exactly when
`r u v` or `r v u`. Orienting each edge `uv` as `u → v` when `r u v` is then a transitive
orientation of `G`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed degree `k`: the instance is a well-formed
instance of CHROMATIC INDEX of `k`-regular graphs (a simple edge list whose graph is
`k`-regular), and its graph is a comparability graph. -/
def WellFormed (k : ℕ) (i : ChromaticIndexRegular.ChromaticIndexRegularInstance) : Prop :=
  ChromaticIndexRegular.WellFormed k i ∧
    ComparabilityGraphSandwich.IsComparabilityGraph (ChromaticIndexRegular.Graph i)

open Classical in
/-- CHROMATIC INDEX of `k`-regular comparability graphs, for the fixed `k`, as a decision
problem over bitstrings. -/
noncomputable def chromaticIndexRegularComparabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChromaticIndexRegular.ChromaticIndexRegularInstance) x with
  | some i => decide (WellFormed k i ∧ ChromaticIndexRegular.ChromaticIndexRegularFeasible k i)
  | none => false

/-- **CHROMATIC INDEX of k-regular comparability graphs is NP-complete for every fixed
`k ≥ 3`.** Source: Cai and Ellis (1991); Galby, Lima, Paulusma and Ries (2019). -/
public theorem_wanted chromaticIndexRegularComparability_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    chromaticIndexRegularComparabilityDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (chromaticIndexRegularComparabilityDec k)

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegularComparability
