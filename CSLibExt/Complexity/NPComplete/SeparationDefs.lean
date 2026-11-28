/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEPARATION: definitions

Source:
J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some variants of the bandwidth minimization
problem", SIAM Journal on Computing 13 (1984), 650-667, doi:10.1137/0213040 (abstract: "the
separation problem which asks if there is a linear layout such that every pair of adjacent
vertexes have a distance greater than k ... the separation and cycle-separation problems are
both NP-complete for each fixed k ≥ 1"; the full text was not available to us);
Z. Miller and D. Pritikin, "On the separation number of a graph", Networks 19 (1989), 651-666,
doi:10.1002/net.3230190604 (restates the result: the problem "given a graph G and an integer k,
is the quantity defined above greater than k?" is NP-complete, even for the case k = 1, by a
simple reduction from the Hamiltonian path problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the dual problem).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Separation

open Bandwidth (BandwidthInstance)

/-- Well-formedness of an instance: a well-formed BANDWIDTH instance (simple edge list) with
`0 < K`. -/
def WellFormed (i : BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ 0 < i.2.2

/-- A linear layout in which the endpoints of every edge are at distance greater than `K`. -/
def SeparationFeasible (i : BandwidthInstance) : Prop :=
  ∃ perm : List ℕ, perm.Perm (List.range i.1) ∧
    ∀ e ∈ i.2.1, i.2.2 < Nat.dist (perm.idxOf e.1) (perm.idxOf e.2)

open Classical in
/-- SEPARATION as a decision problem over bitstrings. -/
noncomputable def separationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ SeparationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Separation
