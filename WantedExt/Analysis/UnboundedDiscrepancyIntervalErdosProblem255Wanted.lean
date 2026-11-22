/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Unbounded discrepancy on some interval (Erdős Problem 255)

Erdős Problem 255: for a sequence `z₁, z₂, … ∈ [0, 1]` let `D_N(I) = #{n ≤ N : z_n ∈ I} - N |I|`.
Must some interval `I ⊆ [0, 1]` have `limsup_N |D_N(I)| = ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.Analysis.UnboundedDiscrepancyIntervalErdosProblem255Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #255, https://www.erdosproblems.com/255 (status PROVED
(LEAN)). UnsolvedMath record UM-30006795 (`EP-255`), dataset ulamai/UnsolvedMath v1.8.0.

The sequence is `z 0, z 1, …` (indices shifted by one, which changes `D_N` by at most one).
Intervals are closed, `[a, b]` with `0 ≤ a < b ≤ 1`; Schmidt's theorem gives intervals `[0, x]`, so
this choice is covered. Since a real sequence is unbounded exactly when its limsup is `∞` (finitely
many terms are bounded), `limsup_N |D_N| = ∞` is stated as unboundedness.
-/

open Classical in
/-- The discrepancy `D_N([a, b]) = #{n < N : z n ∈ [a, b]} - N (b - a)` of the first `N` terms
`z 0, …, z (N - 1)` of a sequence (the source's `z₁, …, z_N`). -/
noncomputable def discrepancy (z : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => z n ∈ Set.Icc a b).card : ℝ) - N * (b - a)

/-- Erdős Problem 255: every sequence in `[0, 1]` has an interval `[a, b] ⊆ [0, 1]` with `a < b`
on which `|D_N([a, b])|` is unbounded, i.e. `limsup_N |D_N([a, b])| = ∞`. -/
def unboundedDiscrepancyInterval : Prop :=
  ∀ z : ℕ → ℝ, (∀ n, z n ∈ Set.Icc (0 : ℝ) 1) →
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ ∀ M : ℝ, ∃ N : ℕ, M < |discrepancy z a b N|

/--
Resolved true: Schmidt proved that for every sequence in `[0, 1]` some interval has unbounded
discrepancy, and later that all but countably many intervals `[0, x]` do. erdosproblems.com/255
lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #255,
https://www.erdosproblems.com/255 (status PROVED (LEAN)); resolution: W. M. Schmidt, Irregularities
of distribution, Quart. J. Math. Oxford Ser. (2) (1968), 181-191, erdosproblems.com/255: answered
yes by Schmidt [Sc68]; Schmidt, Irregularities of distribution. VI, Compositio Math. (1972), 63-74,
shows it for all but countably many intervals [0, x], https://www.erdosproblems.com/255.
-/
public theorem_wanted unboundedDiscrepancyInterval_holds : unboundedDiscrepancyInterval

end MathlibExt.Analysis.UnboundedDiscrepancyIntervalErdosProblem255Wanted
