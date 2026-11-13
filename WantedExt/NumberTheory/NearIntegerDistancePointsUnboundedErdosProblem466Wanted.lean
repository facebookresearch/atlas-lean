/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Points with distances far from integers, lower bound (Erdős Problem 466)

Erdős Problem 466: with `N(X, δ)` as in Problem 465, is there `δ > 0` with `N(X, δ) → ∞` as `X → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.NumberTheory.NearIntegerDistancePointsShared

@[expose] public section

namespace MathlibExt.NumberTheory.NearIntegerDistancePointsUnboundedErdosProblem466Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #466, https://www.erdosproblems.com/466 (status
PROVED). UnsolvedMath record UM-30006885 (`EP-466`), dataset ulamai/UnsolvedMath v1.8.0.

`‖x‖ = |x - round x|`. `N(X, δ) → ∞` is unfolded: for every `M`, every disc of large radius `X`
contains an admissible configuration of at least `M` points. Compared with the formal-conjectures
statement `ErdosProblems/466.lean` (equivalent; no code imported).
-/

open MathlibExt.NumberTheory.NearIntegerDistancePointsShared

/-- Erdős Problem 466: there is `δ > 0` with `N(X, δ) → ∞` as `X → ∞`. For every `M`, every disc
of large radius `X` contains an admissible configuration of at least `M` points. -/
def nearIntegerDistancePointsUnbounded : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), IsNearIntegerAvoiding X δ P ∧ M ≤ P.card

/--
Resolved true: Graham proved `N(X, 1/10) > (log X) / 10`, so `δ = 1/10` works; Sárközy later proved
`N(X, δ) > X ^ (1/2 - δ ^ (1/7))` for all small `δ > 0`. Source: T. F. Bloom, Erdős Problems,
Problem #466, https://www.erdosproblems.com/466 (status PROVED); resolution: R. L. Graham (as
recorded on erdosproblems.com/466); A. Sárközy, On distances near integers. I, II, Studia Sci. Math.
Hungar. (1976), 37-50, 105-111, erdosproblems.com/466: Graham proved N(X, 1/10) > (log X)/10;
Sárközy proved N(X, δ) > X^{1/2 - δ^{1/7}} for small δ, https://www.erdosproblems.com/466.
-/
public theorem_wanted nearIntegerDistancePointsUnbounded_holds : nearIntegerDistancePointsUnbounded

end MathlibExt.NumberTheory.NearIntegerDistancePointsUnboundedErdosProblem466Wanted
