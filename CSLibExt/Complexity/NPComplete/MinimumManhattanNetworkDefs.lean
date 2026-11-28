/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MANHATTAN NETWORK: definitions

Source:
F. Y. L. Chin, Z. Guo and H. Sun, "Minimum Manhattan network is NP-complete", Discrete and
Computational Geometry 45(4) (2011), 701-722, doi:10.1007/s00454-011-9342-z.
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumManhattanNetwork

/-- An instance: the points of `T`, each a pair of integer coordinates given as
(positive part, negative part) pairs, and the bound `L`. -/
abbrev MinimumManhattanNetworkInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The points of `T` in the real plane. -/
noncomputable def points (i : MinimumManhattanNetworkInstance) : List (ℝ × ℝ) :=
  i.1.map fun c => ((((c.1.1 : ℤ) - c.1.2 : ℤ) : ℝ), (((c.2.1 : ℤ) - c.2.2 : ℤ) : ℝ))

/-- The `L₁` (rectilinear) distance `|x - x'| + |y - y'|`. -/
noncomputable def l1Dist (a b : ℝ × ℝ) : ℝ :=
  |a.1 - b.1| + |a.2 - b.2|

/-- `w` is a rectilinear path in the set `U`: consecutive points share a coordinate, and the
segment between them lies in `U`. Only consecutive pairs are tested, so a one-point list `[p]`
is a rectilinear path in every set, even one that does not contain `p`. -/
def IsRectilinearPathIn (U : Set (ℝ × ℝ)) (w : List (ℝ × ℝ)) : Prop :=
  w.IsChain fun a b => (a.1 = b.1 ∨ a.2 = b.2) ∧ segment ℝ a b ⊆ U

/-- The length of the path `w`: the sum of the `L₁` distances of consecutive points. -/
noncomputable def pathLength (w : List (ℝ × ℝ)) : ℝ :=
  ((w.zip w.tail).map fun e => l1Dist e.1 e.2).sum

/-- Well-formedness of an instance: `0 < L`. -/
def WellFormed (i : MinimumManhattanNetworkInstance) : Prop :=
  0 < i.2

/-- Some list `N` of axis-parallel segments of total length at most `L` has, for all points
`p, q` of `T`, a rectilinear path from `p` to `q` in the union of its segments whose length is
the `L₁` distance of `p` and `q`. For `p = q` the one-point path qualifies whether or not `p`
lies on a segment of `N`; the network graph is read with every terminal as a vertex, isolated
ones included, so it may differ from the union of its segments. -/
def MinimumManhattanNetworkFeasible (i : MinimumManhattanNetworkInstance) : Prop :=
  ∃ N : List ((ℝ × ℝ) × (ℝ × ℝ)),
    (∀ s ∈ N, s.1.1 = s.2.1 ∨ s.1.2 = s.2.2) ∧
    (N.map fun s => l1Dist s.1 s.2).sum ≤ i.2 ∧
    ∀ p ∈ points i, ∀ q ∈ points i, ∃ w : List (ℝ × ℝ),
      w.head? = some p ∧ w.getLast? = some q ∧
      IsRectilinearPathIn (⋃ s ∈ N, segment ℝ s.1 s.2) w ∧ pathLength w = l1Dist p q

open Classical in
/-- MINIMUM MANHATTAN NETWORK as a decision problem over bitstrings. -/
noncomputable def minimumManhattanNetworkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumManhattanNetworkInstance) x with
  | some i => decide (WellFormed i ∧ MinimumManhattanNetworkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumManhattanNetwork
