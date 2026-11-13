/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pairs of close divisors (Erdős Problem 449)

Erdős Problem 449: let `r(n)` count the pairs of divisors `d₁ < d₂ < 2d₁` of `n`. Is it true that
for every `ε > 0`, `r(n) < ε τ(n)` for almost all `n`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.CloseDivisorPairsErdosProblem449Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #449, https://www.erdosproblems.com/449 (status
DISPROVED). UnsolvedMath record UM-30006879 (`EP-449`), dataset ulamai/UnsolvedMath v1.8.0.

"Almost all" means natural density `1` (`Set.HasDensity`, MathlibExt). formal-conjectures has no
statement of this problem.
-/

/-- `r(n)`: the number of pairs of divisors `d₁ < d₂ < 2 d₁` of `n`. -/
def closeDivisorPairCount (n : ℕ) : ℕ :=
  ((n.divisors ×ˢ n.divisors).filter fun p => p.1 < p.2 ∧ p.2 < 2 * p.1).card

/-- Erdős Problem 449: for every `ε > 0`, `r(n) < ε τ(n)` for almost all `n` (the set of such `n`
has natural density `1`). -/
def closeDivisorPairCountSmallAlmostAlways : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {n : ℕ | (closeDivisorPairCount n : ℝ) < ε * n.divisors.card}.HasDensity 1

/--
Resolved false: for every `K > 0`, `r(n) > K τ(n)` on a set of positive density: by Cauchy–Schwarz
`r(n) + τ(n) ≥ τ(n)² / τ⁺(n)`, and the negative answer to Problem 448 makes the right side at least
`(K + 1) τ(n)` on such a set (Ford's observation on erdosproblems.com/449; Hall and Tenenbaum,
Divisors, Section 4.6, give the argument for an essentially identical problem). Source: T. F. Bloom,
Erdős Problems, Problem #449, https://www.erdosproblems.com/449 (status DISPROVED); resolution: K.
Ford's observation on erdosproblems.com/449, from the negative answer to Problem 448
(Erdős-Tenenbaum); R. R. Hall and G. Tenenbaum, Divisors (1988), Section 4.6, r(n) > K τ(n) on a set
of positive density, for every K > 0 (erdosproblems.com/449).
-/
public theorem_wanted closeDivisorPairCountSmallAlmostAlways_refuted :
    ¬ closeDivisorPairCountSmallAlmostAlways

end MathlibExt.NumberTheory.CloseDivisorPairsErdosProblem449Wanted
