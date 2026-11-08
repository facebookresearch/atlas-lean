/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integer sequences for diversity statistics

Statements from Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics", *Journal
of Integer Sequences* 29 (2026), Article 26.1.5
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Rosenberg/rosen5.html>).

A sample of size `N` is recorded by its list of type
counts. The Gini-Simpson index is `1 - ∑ (a / N)^2`, so
its number of distinct values `γ(N)` equals the number
of distinct values of `∑ a^2`; the Shannon index is
`-∑ (a / N) log (a / N)` and `σ(N)` counts its distinct
values. The bounds on `γ` were verified by partition
enumeration for `N ≤ 30`.

Not stated (see the source audit table): Propositions
1 and 2 (quoted bounds of Rosenberg relating the
maximal cell probability to `∑ p_i^2` and to the
Shannon index) and Theorem 3 (whose bounding
functions `M_min`, `M_max`, `S_min`, `S_max` are
defined in missing equations).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Probability.DiversityStatisticsWanted

/-- The number of possible values of the Gini-Simpson
index across all samples of size `N`, counted as the
number of distinct sums of squared cell counts. -/
noncomputable def giniSimpsonCount (N : ℕ) : ℕ :=
  Set.ncard {s : ℕ | ∃ l : List ℕ, l.sum = N ∧
    (l.map (fun a => a ^ 2)).sum = s}

/-- The number of possible values of the Shannon
index `-∑ (a / N) log (a / N)` across all samples of
size `N` (with the convention `0 log 0 = 0`, which
matches `Real.log 0 = 0`). -/
noncomputable def shannonCount (N : ℕ) : ℕ :=
  Set.ncard {v : ℝ | ∃ l : List ℕ, l.sum = N ∧
    v = -(l.map (fun a => ((a : ℝ) / N) * Real.log ((a : ℝ) / N))).sum}

/-- **Proposition 4**: `γ(N) ≤ (1 / 2) N^2 - (1 / 2) N + 1`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 4. -/
theorem_wanted giniSimpsonCount_le (N : ℕ) :
    (giniSimpsonCount N : ℚ) ≤ (1 / 2) * N ^ 2 - (1 / 2) * N + 1

/-- **Proposition 5**: `γ(N)` is bounded below by
`(1 / 3) m (m^2 + 3r - 1) + 1`, where `N = C(m + 1, 2) + r`
with `0 ≤ r ≤ m`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 5. -/
theorem_wanted giniSimpsonCount_ge_triangular (N m r : ℕ)
    (hN : N = (m + 1) * m / 2 + r) (hr : r ≤ m) :
    (1 / 3) * (m : ℚ) * ((m : ℚ) ^ 2 + 3 * r - 1) + 1 ≤
      (giniSimpsonCount N : ℚ)

/-- **Proposition 6**: `γ(N)` is bounded below by
`(⌊N^2 / 5⌋ - N) / 2`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 6. -/
theorem_wanted giniSimpsonCount_ge (N : ℕ) :
    (((N ^ 2 / 5 : ℕ) : ℚ) - N) / 2 ≤ (giniSimpsonCount N : ℚ)

/-- **Proposition 7**: `γ(N) ~ (1 / 2) N^2`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 7. -/
theorem_wanted giniSimpsonCount_asymp :
    Filter.Tendsto
      (fun N : ℕ => (giniSimpsonCount N : ℝ) / (N : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 2))

/-- **Proposition 8**: for all `N ≥ 1`,
`σ(N) ≤ exp (π √(2 / 3) √N)`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Proposition 8. -/
theorem_wanted shannonCount_le (N : ℕ) (hN : 1 ≤ N) :
    (shannonCount N : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt (2 / 3) * Real.sqrt N)

/-- **Theorem 9**: `σ(N)` grows faster than every
polynomial: for every (nonzero) polynomial `q`,
`lim_{N → ∞} σ(N) / |q(N)| = ∞`.

Source: Bradley K. Moon and Noah A. Rosenberg,
"Integer Sequences for Diversity Statistics",
Theorem 9. -/
theorem_wanted shannonCount_superpolynomial
    (q : Polynomial ℝ) (hq : q ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ => (shannonCount N : ℝ) / |q.eval (N : ℝ)|)
      Filter.atTop Filter.atTop

end MathlibExt.Probability.DiversityStatisticsWanted
