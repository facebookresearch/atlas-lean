/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Divisors in dyadic intervals (Erdős Problem 448)

Erdős Problem 448: let `τ(n)` count the divisors of `n` and `τ⁺(n)` the number of `k` such that `n`
has a divisor in `[2^k, 2^{k+1})`. Is it true that for all `ε > 0`, `τ⁺(n) < ε τ(n)` for almost all
`n`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.DyadicDivisorClassesErdosProblem448Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #448, https://www.erdosproblems.com/448 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006878 (`EP-448`), dataset ulamai/UnsolvedMath v1.8.0.

`τ⁺(n)` is the number of distinct values `⌊log₂ d⌋` over the divisors `d` of `n`. "Almost all" means
natural density `1` (`Set.HasDensity`, MathlibExt). Compared with the formal-conjectures statement
`ErdosProblems/448.lean` (equivalent; no code imported).
-/

/-- `τ⁺(n)`: the number of `k` such that `n` has a divisor in `[2^k, 2^(k+1))`, i.e. the number of
distinct values `⌊log₂ d⌋` over the divisors `d` of `n`. -/
def dyadicDivisorClassCount (n : ℕ) : ℕ :=
  (n.divisors.image (Nat.log 2)).card

/-- Erdős Problem 448: for every `ε > 0`, `τ⁺(n) < ε τ(n)` for almost all `n` (the set of such
`n` has natural density `1`). -/
def dyadicDivisorClassCountSmallAlmostAlways : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {n : ℕ | (dyadicDivisorClassCount n : ℝ) < ε * n.divisors.card}.HasDensity 1

/--
Resolved false: Erdős and Tenenbaum showed that the upper density of `{n : τ⁺(n) < ε τ(n)}` is `≍
ε^{1 - o(1)}`, in particular less than `1` for small `ε`; Hall and Tenenbaum sharpened this to `≪ ε
log(2/ε)` (erdosproblems.com/448). Source: T. F. Bloom, Erdős Problems, Problem #448,
https://www.erdosproblems.com/448 (status DISPROVED (LEAN)); resolution: P. Erdős and G. Tenenbaum,
Sur la structure de la suite des diviseurs d'un entier, Ann. Inst. Fourier (Grenoble) 31 (1981),
17-37, the upper density of {n : τ⁺(n) < ε τ(n)} is ≍ ε^{1-o(1)} (erdosproblems.com/448).
-/
public theorem_wanted dyadicDivisorClassCountSmallAlmostAlways_refuted :
    ¬ dyadicDivisorClassCountSmallAlmostAlways

end MathlibExt.NumberTheory.DyadicDivisorClassesErdosProblem448Wanted
