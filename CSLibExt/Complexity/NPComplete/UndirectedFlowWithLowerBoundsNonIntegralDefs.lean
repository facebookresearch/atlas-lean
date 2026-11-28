/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED FLOW WITH LOWER BOUNDS with non-integral flows: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 216, problem [ND37] UNDIRECTED FLOW
WITH LOWER BOUNDS, comment: "Problem is NP-complete in the strong sense, even if
non-integral flows are allowed";
A. Itai, "Two-commodity flow", Journal of the ACM 25 (1978), 596-611,
doi:10.1145/322092.322100 (the reference Garey and Johnson give for [ND37]).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral

open MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- There is a real-valued flow `f` from `s` to `t` that is feasible for the symmetric edge
capacities (it is nonnegative, vanishes off the orientations of the edges, is at most
`c({u, v})` on both orientations of `{u, v}`, and is conserved at every vertex other than `s`
and `t`), uses only one direction of each edge, meets each lower bound in the used direction,
and has net flow into `t` at least `R`. -/
def NonIntegralFeasible (i : UndirectedFlowWithLowerBoundsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1) (f : Fin i.1 → Fin i.1 → ℝ),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩ f ∧
      (∀ u v, (Graph i).Adj u v →
        (f u v = 0 ∨ f v u = 0) ∧ (lowerBound i u v : ℝ) ≤ max (f u v) (f v u)) ∧
      (i.2.2.2.2 : ℝ) ≤ (∑ u, f u ⟨i.2.2.2.1, ht⟩) - ∑ w, f ⟨i.2.2.2.1, ht⟩ w

open Classical in
/-- UNDIRECTED FLOW WITH LOWER BOUNDS with non-integral flows, as a decision problem over
bitstrings. -/
noncomputable def nonIntegralDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UndirectedFlowWithLowerBoundsInstance) x with
  | some i => decide (WellFormed i ∧ NonIntegralFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral
