/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Many monochromatic sums in colourings of `{1, …, N}` (Erdős Problem 484)

Erdős Problem 484 (Roth): is there an absolute `c > 0` such that for every `k`-colouring of `{1, …,
N}` (`N` large in terms of `k`) at least `c N` integers of `{1, …, N}` are sums `a + b` with `a ≠ b`
in `{1, …, N}` of the same colour?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #484, https://www.erdosproblems.com/484 (status PROVED
(LEAN)). UnsolvedMath record UM-30006894 (`EP-484`), dataset ulamai/UnsolvedMath v1.8.0.

A colouring is any `f : ℕ → Fin k`; only its values on `{1, …, N}` matter. `c` does not depend on
`k`; `N₀` does. Compared with the formal-conjectures statement `ErdosProblems/484.lean` (equivalent;
no code imported).
-/

/-- Erdős Problem 484 (Roth): there is an absolute `c > 0` such that for every `k ≥ 1` and all
`N` large in terms of `k`, every `k`-colouring of `{1, …, N}` leaves at least `c N` integers
`n ∈ {1, …, N}` of the form `a + b` with `a ≠ b` in `{1, …, N}` of the same colour. -/
def monochromaticSumsLinearCount : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ f : ℕ → Fin k,
    c * N ≤ ({n : ℕ | n ∈ Finset.Icc 1 N ∧
      ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n}.ncard : ℝ)

/--
Resolved true: Erdős, Sárközy and Sós proved that at least `N/2 - O(N ^ (1 - 1/2^(k+1)))` even
numbers in `{1, …, N}` are monochromatic sums, so any `c < 1/2` works. Source: T. F. Bloom, Erdős
Problems, Problem #484, https://www.erdosproblems.com/484 (status PROVED (LEAN)); resolution: P.
Erdős, A. Sárközy and V. T. Sós, On a conjecture of Roth and some related problems. I (1989), 47-59,
erdosproblems.com/484: at least N/2 - O(N^{1 - 1/2^{k+1}}) even numbers are monochromatic sums,
https://www.erdosproblems.com/484.
-/
public theorem_wanted monochromaticSumsLinearCount_holds : monochromaticSumsLinearCount

end MathlibExt.Combinatorics.MonochromaticSumsLinearErdosProblem484Wanted
