/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC STEINER TREE in the L∞ metric: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC STEINER TREE, p. 209
(comment: "Remains so if the distance measure is replaced by the L₁ "rectilinear" metric,
|x₁ − x₂| + |y₁ − y₂|, [Garey and Johnson, 1977a] or the L∞ metric, max {|x₁ − x₂|, |y₁ − y₂|},
which is equivalent to L₁ under a 45° rotation");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RectilinearSteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree

open RectilinearSteinerTree (RectilinearSteinerTreeInstance points)

/-- The `L∞` distance `max {|x₁ - x₂|, |y₁ - y₂|}`. -/
def chebyshev (a b : ℤ × ℤ) : ℤ := max |a.1 - b.1| |a.2 - b.2|

/-- The `L∞` distance between the endpoints of an unordered pair of points. -/
def edgeWeight {V : Finset (ℤ × ℤ)} : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => chebyshev a b, fun a b => by
    simp only [chebyshev, abs_sub_comm (a : ℤ × ℤ).1, abs_sub_comm (a : ℤ × ℤ).2]⟩

/-- The total weight of a graph on a finite set of points: the sum of the `L∞` lengths of its
edges. -/
noncomputable def totalWeight {V : Finset (ℤ × ℤ)} (T : SimpleGraph V) : ℤ :=
  ∑ᶠ e ∈ T.edgeSet, edgeWeight e

/-- Some finite `Q ⊆ ℤ × ℤ` and some tree `T` on the vertex set `P ∪ Q` have total `L∞`
weight at most `K`. -/
def LInfinitySteinerTreeFeasible (i : RectilinearSteinerTreeInstance) : Prop :=
  ∃ Q : Finset (ℤ × ℤ), ∃ T : SimpleGraph ↥(points i ∪ Q), T.IsTree ∧
    totalWeight T ≤ i.2

open Classical in
/-- GEOMETRIC STEINER TREE in the `L∞` metric as a decision problem over bitstrings. -/
noncomputable def lInfinitySteinerTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectilinearSteinerTreeInstance) x with
  | some i => decide (RectilinearSteinerTree.WellFormed i ∧ LInfinitySteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree
