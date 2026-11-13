/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integers with two divisors within a factor of two (Erdős Problem 144)

Erdős Problem 144: the density of integers which have two divisors `d₁ < d₂ < 2 d₁` exists and is
equal to `1`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.CloseDivisorPairDensityErdosProblem144Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #144, https://www.erdosproblems.com/144 (status PROVED
(LEAN)). UnsolvedMath record UM-30006740 (`EP-144`), dataset ulamai/UnsolvedMath v1.8.0.

Natural density is the repository's `Set.HasDensity`. The stronger form with `2` replaced by any
constant `c > 1` (asked in a later source) is not stated. formal-conjectures has no statement.
-/

/-- Erdős Problem 144: the integers with two divisors `d₁ < d₂ < 2 d₁` have natural density `1`. -/
def closeDivisorPairDensityOne : Prop :=
  {n : ℕ | ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁}.HasDensity 1

/--
Resolved true: Maier and Tenenbaum proved that almost all integers have two divisors `d₁ < d₂ < c
d₁` for every fixed `c > 1`, in particular for `c = 2`; erdosproblems.com/144 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #144, https://www.erdosproblems.com/144 (status
PROVED (LEAN)); resolution: H. Maier and G. Tenenbaum, On the set of divisors of an integer, Invent.
Math. 76 (1984), 121-128, erdosproblems.com/144: proved by Maier and Tenenbaum, also with 2 replaced
by any c > 1.
-/
public theorem_wanted closeDivisorPairDensityOne_holds : closeDivisorPairDensityOne

end MathlibExt.NumberTheory.CloseDivisorPairDensityErdosProblem144Wanted
