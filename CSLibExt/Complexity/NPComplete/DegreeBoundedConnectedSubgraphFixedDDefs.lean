/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE-BOUNDED CONNECTED SUBGRAPH with a fixed degree bound `d ≥ 2`: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphFixedD

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

end MetaMathlibExt.Complexity.NPComplete.DegreeBoundedConnectedSubgraphFixedD
