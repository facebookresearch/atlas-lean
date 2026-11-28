/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM K-CONNECTED SUBGRAPH for fixed K ≥ 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT31] MINIMUM K-CONNECTED
SUBGRAPH, p. 198 (comment: "Both problems remain NP-complete for any fixed K ≥ 2 and can be
solved trivially in polynomial time for K = 1"; reference: Chung and Graham, 1977).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumKConnectedSubgraphDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraphFixedK

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, edge budget `B`; the
connectivity `K` is fixed. -/
abbrev MinimumKConnectedSubgraphFixedKInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The [GT31] instance `(n, E, K, B)` of an instance `(n, E, B)` and the fixed `K`. -/
def withK (K : ℕ) (i : MinimumKConnectedSubgraphFixedKInstance) :
    MinimumKConnectedSubgraph.MinimumKConnectedSubgraphInstance :=
  (i.1, i.2.1, K, i.2.2)

open Classical in
/-- MINIMUM K-CONNECTED SUBGRAPH for a fixed `K` as a decision problem over bitstrings. -/
noncomputable def minimumKConnectedSubgraphFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKConnectedSubgraphFixedKInstance) x with
  | some i => decide (MinimumKConnectedSubgraph.WellFormed (withK K i) ∧
      MinimumKConnectedSubgraph.MinimumKConnectedSubgraphFeasible (withK K i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumKConnectedSubgraphFixedK
