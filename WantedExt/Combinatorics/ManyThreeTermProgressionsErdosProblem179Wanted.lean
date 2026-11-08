/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with many three-term progressions (Erdős Problem 179)

Erdős Problem 179: let `F_k(N, ℓ)` be the least number such that every `N`-element set of integers
with at least `F_k(N, ℓ)` `k`-term arithmetic progressions contains an `ℓ`-term progression. Is
`F₃(N, 4) = o(N²)`? Is `lim_{N → ∞} log F₃(N, ℓ) / log N = 2` for every `ℓ > 3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status
PROVED). UnsolvedMath record UM-30006752 (`EP-179`), dataset ulamai/UnsolvedMath v1.8.0.

Sets are finite subsets of `ℕ` (the count is translation invariant). A `k`-term progression is a
pair `(a, d)` with `d ≥ 1` and `a + i d ∈ A` for `i < k`; for `k ≥ 2` such `a, d` are at most `max
A` and `(a, d) ↦ (a, a + d)` is injective, so the count is at most `N²`, `F_k(N, ℓ)` is the infimum
of a nonempty set, and `F₃(N, ℓ) ≥ 1` (sets of powers of `2` have no `3`-term progression). The
open-ended "find good upper bounds" is not formalized.
-/

open Filter Topology Asymptotics

/-- `A` contains a `k`-term arithmetic progression `a, a + d, …, a + (k - 1) d` with `d ≥ 1`. -/
def HasAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- The number of `k`-term arithmetic progressions in `A`, `k ≥ 2`: pairs `(a, d)` with `d ≥ 1` and
`a + i d ∈ A` for all `i < k` (such `a, d` are at most `max A`). -/
def apCount (A : Finset ℕ) (k : ℕ) : ℕ :=
  ((A ×ˢ Finset.Icc 1 (A.sup id)).filter (fun p => ∀ i < k, p.1 + i * p.2 ∈ A)).card

/-- `F_k(N, ℓ)`: the least `m` such that every `N`-element set `A ⊆ ℕ` containing at least `m`
`k`-term arithmetic progressions contains an `ℓ`-term arithmetic progression. -/
noncomputable def apThreshold (k ℓ N : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset ℕ, A.card = N → m ≤ apCount A k → HasAP A ℓ}

/-- Erdős Problem 179, first question: `F₃(N, 4) = o(N²)`. -/
def threeAPThresholdForFourAPLittleO : Prop :=
  (fun N : ℕ => (apThreshold 3 4 N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2)

/-- Erdős Problem 179, second question: `log F₃(N, ℓ) / log N → 2` for every `ℓ > 3`. -/
def threeAPThresholdExponentTwo : Prop :=
  ∀ ℓ : ℕ, 3 < ℓ →
    Tendsto (fun N : ℕ => Real.log (apThreshold 3 ℓ N) / Real.log N) atTop (𝓝 2)

/--
Resolved true: Fox and Pohoata bound `F_k(N, ℓ)` above by `(r_ℓ(N) / N)^{O(1)} N²`, with `r_ℓ(N)`
the largest size of a subset of `{1, …, N}` without `ℓ`-term progressions, which is `o(N²)` by
Szemerédi's theorem; erdosproblems.com/179 records `F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ}`. Source: T.
F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED);
resolution: J. Fox and C. Pohoata, Sets without k-term progressions can have many shorter
progressions, Random Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for
all k > s ≥ 3, log f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of
s-term progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² /
(log log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem_wanted threeAPThresholdForFourAPLittleO_holds : threeAPThresholdForFourAPLittleO

/--
Resolved true: Fox and Pohoata prove `lim log f_{s,k}(n) / log n = 2` for all `k > s ≥ 3`, where
`f_{s,k}(n)` is the largest number of `s`-term progressions in an `n`-element set with no `k`-term
progression, so that `F_s(n, k) = f_{s,k}(n) + 1`; take `s = 3` and `k = ℓ`. Source: T. F. Bloom,
Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED); resolution: J. Fox
and C. Pohoata, Sets without k-term progressions can have many shorter progressions, Random
Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for all k > s ≥ 3, log
f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of s-term
progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² / (log
log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem_wanted threeAPThresholdExponentTwo_holds : threeAPThresholdExponentTwo

end MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted
