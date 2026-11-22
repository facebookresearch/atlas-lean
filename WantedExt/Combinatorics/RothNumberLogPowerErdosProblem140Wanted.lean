/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Roth numbers below every power of the logarithm (Erdős Problem 140)

Erdős Problem 140: let `r₃(N)` be the size of the largest subset of `{1, …, N}` with no non-trivial
three-term arithmetic progression. Prove that `r₃(N) ≪ N/(log N)^C` for every `C > 0`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.RothNumberLogPowerErdosProblem140Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #140, https://www.erdosproblems.com/140 (status PROVED
(LEAN)). UnsolvedMath record UM-30006739 (`EP-140`), dataset ulamai/UnsolvedMath v1.8.0.

`r₃(N)` is Mathlib's `rothNumberNat N` (subsets of `{0, …, N - 1}`, the same value by translation);
`≪` is a constant depending on `C`, for all `N ≥ 2`. formal-conjectures has no statement.
-/

/-- Erdős Problem 140: for every `C > 0`, `r₃(N) ≪ N / (log N)^C`, where `r₃(N) = rothNumberNat N`
is the largest size of a subset of `{0, …, N - 1}` with no non-trivial three-term arithmetic
progression. -/
def rothNumberLogPowerDecay : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N → (rothNumberNat N : ℝ) ≤ K * N / Real.log N ^ C

/--
Resolved true: Kelley and Meka proved that for some `β > 0` every subset of `{1, …, N}` of size at
least `2^{-O((log N)^β)} N` contains a non-trivial three-term progression, so `r₃(N) ≤ N exp(-c (log
N)^β)`, which is `≪ N/(log N)^C` for every `C`; erdosproblems.com/140 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #140, https://www.erdosproblems.com/140 (status PROVED
(LEAN)); resolution: Z. Kelley and R. Meka, Strong bounds for 3-progressions, FOCS 2023,
arXiv:2302.05537, abstract: every A ⊆ {1, …, N} with |A| ≥ 2^{-O((log N)^β)} N contains a
non-trivial 3-term progression; erdosproblems.com/140, https://arxiv.org/abs/2302.05537.
-/
public theorem_wanted rothNumberLogPowerDecay_holds : rothNumberLogPowerDecay

end MathlibExt.Combinatorics.RothNumberLogPowerErdosProblem140Wanted
