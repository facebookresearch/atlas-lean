/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED BANDWIDTH for rooted directed trees with out-degree at most 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT41] DIRECTED BANDWIDTH, p. 200
(comment: "Remains NP-complete for rooted directed trees with maximum in-degree 1 and maximum
out-degree at most 2.");
M. R. Garey, R. L. Graham, D. S. Johnson, and D. E. Knuth, "Complexity results for bandwidth
minimization", SIAM Journal on Applied Mathematics 34 (1978), 477-495, doi:10.1137/0134037,
Section 9.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Orientation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Card
public import CSLibExt.Complexity.NPComplete.DirectedBandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedBandwidthRootedTrees

open MetaMathlibExt.Complexity.NPComplete.DirectedBandwidth (DirectedBandwidthInstance)

/-- The digraph of the instance on `Fin n`: an arc `u → v` when `(u, v)` is listed. -/
def Graph (i : DirectedBandwidthInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: a well-formed DIRECTED BANDWIDTH instance whose underlying
undirected graph is a tree, in which every vertex has at most 1 distinct in-neighbour and at most
2 distinct out-neighbours. -/
def WellFormed (i : DirectedBandwidthInstance) : Prop :=
  DirectedBandwidth.WellFormed i ∧ (Graph i).toSimpleGraphInclusive.IsTree ∧
    ∀ v, ((Finset.range i.1).filter fun u => (u, v) ∈ i.2.1).card ≤ 1 ∧
      ((Finset.range i.1).filter fun w => (v, w) ∈ i.2.1).card ≤ 2

open Classical in
/-- DIRECTED BANDWIDTH for rooted directed trees with out-degree at most 2, as a decision
problem over bitstrings. -/
noncomputable def directedBandwidthRootedTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DirectedBandwidthInstance) x with
  | some i => decide (WellFormed i ∧ DirectedBandwidth.DirectedBandwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DirectedBandwidthRootedTrees
