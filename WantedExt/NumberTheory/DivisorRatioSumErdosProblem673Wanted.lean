/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sums of ratios of consecutive divisors (Erdős Problem 673)

Erdős Problem 673: let `1 = d₁ < ⋯ < d_{τ(n)} = n` be the divisors of `n` and `G(n) = ∑_{1 ≤ i <
τ(n)} d_i / d_{i+1}`. Is it true that `G(n) → ∞` for almost all `n`? Can one prove an asymptotic
formula for `∑_{n ≤ X} G(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorRatioSumErdosProblem673Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #673, https://www.erdosproblems.com/673 (status
PROVED). UnsolvedMath record UM-30006977 (`EP-673`), dataset ulamai/UnsolvedMath v1.8.0.

"Almost all" means natural density `1` (`Set.HasDensity`, MathlibExt). `G(n) → ∞` for almost all `n`
is read as: for every `K` the set of `n` with `G(n) > K` has density `1`. Only the first question is
formalized; the second (an asymptotic formula) is not recorded as answered on the problem page.
Compared with the formal-conjectures statement `ErdosProblems/673.lean` (same first part;
formal-conjectures also states `∑ G(n) ∼ X log X`, which this module does not; no code imported).
-/

/-- `G(n) = ∑_{1 ≤ i < τ(n)} d_i / d_{i+1}`, where `1 = d_1 < ⋯ < d_{τ(n)} = n` are the divisors
of `n`: the sum of the ratios of consecutive entries of the increasing list of divisors. -/
noncomputable def divisorRatioSum (n : ℕ) : ℝ :=
  (((n.divisors.sort (· ≤ ·)).zip (n.divisors.sort (· ≤ ·)).tail).map
    fun p : ℕ × ℕ => (p.1 : ℝ) / p.2).sum

/-- Erdős Problem 673, first question: `G(n) → ∞` for almost all `n`, i.e. for every `K` the set
of `n` with `G(n) > K` has natural density `1`. -/
def divisorRatioSumTendsToInfinityAlmostAll : Prop :=
  ∀ K : ℝ, {n : ℕ | K < divisorRatioSum n}.HasDensity 1

/--
Resolved true: by Tao's bounds `τ(n/m)/m ≤ G(n) ≤ τ(n)` for every divisor `m > 1` of `n` (for
example `τ(n)/4 ≤ G(n)` for even `n`), `G(n)` grows like `τ(n)`; erdosproblems.com/673 records that
the answer to the first question is yes, and Erdős himself called it trivial in 1982. Source: T. F.
Bloom, Erdős Problems, Problem #673, https://www.erdosproblems.com/673 (status PROVED); resolution:
erdosproblems.com/673 (T. Tao's observation); P. Erdős, Some of my favourite problems which recently
have been solved (1982), 59-79, erdosproblems.com/673: Tao observed τ(n/m)/m ≤ G(n) ≤ τ(n) for every
divisor m > 1 of n, so G(n) behaves like τ(n) and 'the answer to the first question is yes'; in
[Er82e] Erdős observes that G(n) → ∞ for almost all n is trivial, https://www.erdosproblems.com/673.
-/
public theorem_wanted divisorRatioSumTendsToInfinityAlmostAll_holds :
    divisorRatioSumTendsToInfinityAlmostAll

end MathlibExt.NumberTheory.DivisorRatioSumErdosProblem673Wanted
