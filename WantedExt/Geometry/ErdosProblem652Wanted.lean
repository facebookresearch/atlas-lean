/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 652
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Geometry.Metric

@[expose] public section

namespace MathlibExt.Geometry.ErdosProblem652Wanted

/-! Source record `EP-652` (Erdős Problem 652). -/

/-- The real Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Count of points of `X` with pinned-distance count below a threshold,
from [EP-652], via the shared `distinctDistancesFrom` API. -/
noncomputable def countSmallPoints (X : Finset Plane) (threshold : ℝ) : ℕ := by
  classical
  exact (X.filter (fun x => (distinctDistancesFrom X x : ℝ) < threshold)).card

/-- The `k`-th order statistic bound from [EP-652]: some `n`-point planar
set has `k`-th smallest `R`-value below `bound * √n`, characterized by at
least `k` points satisfying the bound. -/
def HasSmallKth (n k : ℕ) (bound : ℝ) : Prop :=
  ∃ X : Finset Plane, X.card = n ∧
    k ≤ countSmallPoints X (bound * Real.sqrt (n : ℝ))

/-- Admissibility of a constant for fixed `k` from [EP-652]: eventually in
`n` there is an `n`-point set whose `k`-th smallest `R`-value is below
the bound. -/
def isAdmissibleBound (k : ℕ) (bound : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasSmallKth n k bound

/-- The minimal constant `αₖ` from [EP-652], formalized as the infimum of
admissible bounds. -/
noncomputable def erdosAlpha (k : ℕ) : ℝ :=
  sInf { bound : ℝ | isAdmissibleBound k bound }

/-- The question of [EP-652]: is it true that `αₖ → ∞` as `k → ∞`. -/
def conjecture : Prop :=
  Filter.Tendsto erdosAlpha Filter.atTop Filter.atTop

/--
Resolved true: Mathialagan (Electron. J. Combin. 28(4) (2021) P4.33, arXiv:1912.01883) proved
that for 2 <= m <= n^(1/3), some point of an m-set determines Omega(sqrt(mn)) distances to an
n-set; with Elekes's circle-grid construction this gives alpha_k = Theta(sqrt(k)), so alpha_k
tends to infinity. Source: S. Mathialagan, On bipartite distinct distances in the plane,
Electronic Journal of Combinatorics 28(4) (2021) P4.33, arXiv:1912.01883,
https://arxiv.org/abs/1912.01883. Moved from `OpenConjectures/Geometry/ErdosProblem652`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem652Wanted
