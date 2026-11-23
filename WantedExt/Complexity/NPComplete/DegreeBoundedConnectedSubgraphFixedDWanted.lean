/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-BOUNDED CONNECTED SUBGRAPH with a fixed degree bound `d ≥ 2` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT26]
DEGREE-BOUNDED CONNECTED SUBGRAPH, p. 196 (comment: "Remains NP-complete for any fixed
`d ≥ 2`");
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355;
M. Yannakakis, "Edge-deletion problems", SIAM Journal on Computing 10 (1981),
297-309, doi:10.1137/0210021.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphFixedD

/-!
# DEGREE-BOUNDED CONNECTED SUBGRAPH with a fixed degree bound `d ≥ 2` is NP-complete

For a fixed constant `d ≥ 2`: INSTANCE: a graph `G = (V, E)` and a positive integer
`K ≤ |E|`. QUESTION: is there a subset `E' ⊆ E` with `|E'| ≥ K` such that the subgraph
`G' = (V, E')` is connected and has no vertex with degree exceeding `d`?

This is the restriction of DEGREE-BOUNDED CONNECTED SUBGRAPH ([GT26],
`DegreeBoundedConnectedSubgraphWanted`) to instances whose degree bound is `d`, for a constant
`d` that is not part of the input. The instance type,
`DegreeBoundedConnectedSubgraph.WellFormed` and
`DegreeBoundedConnectedSubgraph.DegreeBoundedConnectedSubgraphFeasible` are the parent's,
unchanged; `WellFormed d` adds that the instance's degree bound is `d`. The parent's condition
`d ≤ |V|` is kept, so for fixed `d` only graphs with at least `d` vertices are instances.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed degree bound `d`: the parent's (a simple edge
list on `Fin n`, degree bound at most `|V|`, `0 < K ≤ |E|`) and the instance's degree bound is
`d`. -/
def WellFormed (d : ℕ)
    (i : DegreeBoundedConnectedSubgraph.DegreeBoundedConnectedSubgraphInstance) : Prop :=
  DegreeBoundedConnectedSubgraph.WellFormed i ∧ i.2.2.1 = d

open Classical in
/-- DEGREE-BOUNDED CONNECTED SUBGRAPH with the degree bound fixed to `d`, as a decision problem
over bitstrings. -/
noncomputable def degreeBoundedConnectedSubgraphFixedDDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeBoundedConnectedSubgraph.DegreeBoundedConnectedSubgraphInstance) x with
  | some i => decide (WellFormed d i ∧
      DegreeBoundedConnectedSubgraph.DegreeBoundedConnectedSubgraphFeasible i)
  | none => false

/-- **DEGREE-BOUNDED CONNECTED SUBGRAPH is NP-complete for every fixed degree bound `d ≥ 2`.**
Source: Garey and Johnson (1979), [GT26], comment; Yannakakis (1978); Yannakakis (1981). -/
public theorem_wanted degreeBoundedConnectedSubgraphFixedD_npComplete (d : ℕ) (hd : 2 ≤ d) :
    degreeBoundedConnectedSubgraphFixedDDec d ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (degreeBoundedConnectedSubgraphFixedDDec d)

end MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphFixedD
