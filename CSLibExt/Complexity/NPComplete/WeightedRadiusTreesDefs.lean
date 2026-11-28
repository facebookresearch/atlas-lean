/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED RADIUS for trees: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT65] WEIGHTED DIAMETER (p. 205),
comments "NP-complete in the strong sense, even if G is a tree. The variant in which 'diameter'
is replaced by 'radius' has the same complexity" (credited there to Perl and Zaks, 1978);
Y. Perl and S. Zaks, "On the complexity of edge labelings for trees", Theoretical Computer
Science 19 (1982), 1-16, doi:10.1016/0304-3975(82)90011-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.WeightedDiameterDefs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedRadiusTrees

open MetaMathlibExt.Complexity.NPComplete.WeightedDiameter
  (WeightedDiameterInstance Graph weightedLength)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, `|C| = |E|`,
`0 < K`) and the graph is a tree. -/
def WellFormed (i : WeightedDiameterInstance) : Prop :=
  WeightedDiameter.WellFormed i ∧ (Graph i).IsTree

/-- Some assignment of the members of `C` to the edges, one member per edge, gives `G` radius at
most `K`: a rearrangement `ℓ` of `C` (the `k`-th listed edge gets length `ℓ[k]`) and a centre `c`
joined to every vertex by a path of length at most `K`. -/
def WeightedRadiusFeasible (i : WeightedDiameterInstance) : Prop :=
  ∃ ℓ : List ℕ, ℓ.Perm i.2.2.1 ∧
    ∃ c : Fin i.1, ∀ v : Fin i.1,
      ∃ p : (Graph i).Walk c v, p.IsPath ∧ weightedLength i ℓ p ≤ i.2.2.2

open Classical in
/-- WEIGHTED RADIUS for trees as a decision problem over bitstrings. -/
noncomputable def weightedRadiusTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedDiameterInstance) x with
  | some i => decide (WellFormed i ∧ WeightedRadiusFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeightedRadiusTrees
