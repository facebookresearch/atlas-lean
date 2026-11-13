/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# N lines in R³ have Θ(N^{3/2}) joints at most (AIM additive combinatorics, Problem 3.13)

AIM workshop Recent trends in additive combinatorics, Problem 3.13 (T. Tao): take `n` lines in `ℝ³`.
Define a joint to be a point with three lines passing through it that are not coplanar. How many
joints can there be? Remark: it is known that there are at least `n^{3/2}`, and a trivial upper
bound is `n²`.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.LinesInEuclideanThreeSpaceShared

@[expose] public section

namespace MathlibExt.Geometry.JointsThreeHalvesAIMCombinatoricsProblem250Wanted

/-!
Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected by E.
Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.13 (T. Tao) and
its remark. UnsolvedMath record UM-20001125 (`AIM-COMBINATORICS-0250`), dataset ulamai/UnsolvedMath
v1.8.0.

Lines are affine subspaces of `ℝ³` with direction of dimension `1`, and the family is a finite set
of distinct lines. A joint is a point on three lines of the family whose directions span `ℝ³` (three
concurrent lines are non-coplanar exactly then). The joints of finitely many lines form a finite set
(each is the intersection point of two non-parallel lines), so `Set.ncard` counts them. The answer
'order `N^{3/2}`' is stated as the Guth-Katz upper bound together with the grid construction quoted
in the remark and by Guth and Katz (`3k²` axis-parallel lines, `k³` joints).
-/

open MathlibExt.Geometry.LinesInEuclideanThreeSpaceShared

/-- `x` is a joint of the family `L` of lines (`IsLine` and `E3 = ℝ³` come from the shared module
`LinesInEuclideanThreeSpaceShared`): three lines of `L` pass through `x` and their directions span
`ℝ³` (the lines are not coplanar). -/
def IsJoint (L : Finset (AffineSubspace ℝ E3)) (x : E3) : Prop :=
  ∃ l₁ ∈ L, ∃ l₂ ∈ L, ∃ l₃ ∈ L, x ∈ l₁ ∧ x ∈ l₂ ∧ x ∈ l₃ ∧
    l₁.direction ⊔ l₂.direction ⊔ l₃.direction = ⊤

/-- Tao's joints question (AIM, Recent trends in additive combinatorics, Problem 3.13) answered:
`N` lines in `ℝ³` determine `O(N^{3/2})` joints, and the order `N^{3/2}` is attained (the
`3k²` axis-parallel lines through the points of `{1, …, k}³` have `k³` joints). -/
def jointsOrderThreeHalves : Prop :=
  (∃ C : ℝ, ∀ L : Finset (AffineSubspace ℝ E3), (∀ l ∈ L, IsLine l) →
      ({x | IsJoint L x} : Set E3).ncard ≤ C * (L.card : ℝ) ^ ((3 : ℝ) / 2)) ∧
  ∀ k : ℕ, ∃ L : Finset (AffineSubspace ℝ E3), (∀ l ∈ L, IsLine l) ∧ L.card = 3 * k ^ 2 ∧
    k ^ 3 ≤ ({x | IsJoint L x} : Set E3).ncard

/--
Resolved: the maximum number of joints of `N` lines in `ℝ³` has order `N^{3/2}`. Guth and Katz
proved the joints conjecture (their Theorem 1.1): `N` lines form at most `O(N^{3/2})` joints. The
matching lower bound is the construction recorded in the remark and in their introduction: the `3k²`
lines in the coordinate directions through the points of `{1, …, k}³` have the `k³` grid points as
joints. Source: AIM workshop Recent trends in additive combinatorics (2004), problem list collected
by E. Croot and V. F. Lev, https://aimath.org/WWN/additivecomb/additivecomb.pdf, Problem 3.13 (T.
Tao) and its remark; resolution: L. Guth and N. H. Katz, Algebraic methods in discrete analogs of
the Kakeya problem, Adv. Math. 225 (2010), 2828-2839, arXiv:0812.1043, Theorem 1.1: any set of N
lines in ℝ³ forms at most O(N^{3/2}) joints (points where three lines with linearly independent
directions intersect); the introduction notes that the lines in coordinate directions through a
lattice cube give N lines with about N^{3/2} / (3√3) joints,
https://doi.org/10.1016/j.aim.2010.05.015.
-/
public theorem_wanted jointsOrderThreeHalves_holds : jointsOrderThreeHalves

end MathlibExt.Geometry.JointsThreeHalvesAIMCombinatoricsProblem250Wanted
