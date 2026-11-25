/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.AdmissibleFinsetSmallPrimes
public import MathlibExt.NumberTheory.GPYMaynardSieveReduction
public import WantedExt.NumberTheory.PrimeGapBoundsHypotheses
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Small gaps between primes: Maynard's and GPY's theorems

Statements from J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383-413
(numbering of arXiv:1311.4600v3), and D. A. Goldston, J. Pintz and C. Y. Yıldırım,
*Primes in tuples I*, Ann. of Math. 170 (2009), 819-862 (numbering of arXiv:math/0508185v1).

Throughout, `p_n = Nat.nth Nat.Prime n` is the `n`-th prime counted from `p_0 = 2`, and a
statement `lim inf_n (p_{n+m} - p_n) ≤ B` is written `∃ᶠ n in atTop, p_{n+m} - p_n ≤ B`.

Level of distribution. Both papers assume that the primes have level of distribution `ϑ`: an
averaged Bombieri–Vinogradov estimate for moduli up to `x^{ϑ - ε}` (Maynard (1.3) with `π(x; q, a)`,
GPY (1.3)-(1.4) with `θ(N; q, a)`). Here this hypothesis is the conjunction of the existing dyadic
von Mangoldt estimates `Polymath8b.ElliottHalberstamAt θ` for all `θ < ϑ`, and the
Elliott–Halberstam conjecture is `Polymath8b.ElliottHalberstam`, as in
`WantedExt.NumberTheory.PrimeGapBounds`. Passing between the cumulative and dyadic forms, and
between `π`, `θ` and `ψ`, is standard but is not formalised here.
-/

@[expose] public section

namespace WantedExt.NumberTheory.MaynardSmallGaps

open Filter MathlibExt.NumberTheory.GPYMaynard WantedExt.NumberTheory.Polymath8b

/-- **Maynard–Tao theorem: bounded gaps between `m + 1` consecutive primes.** For every natural
number `m` there is `B` such that `p_{n+m} - p_n ≤ B` for infinitely many `n`, that is
`lim inf_n (p_{n+m} - p_n) < ∞` (Maynard, *Small gaps between primes*, arXiv:1311.4600v3,
abstract: "`lim inf_n (p_{n+m} - p_n) < ∞` for every integer `m`"; obtained independently by
Tao). -/
theorem_wanted frequently_nth_prime_add_sub_le_of_exists (m : ℕ) :
    ∃ B : ℕ, ∃ᶠ n in atTop, Nat.nth Nat.Prime (n + m) - Nat.nth Nat.Prime n ≤ B

/-- **Maynard's explicit bound for gaps between `m + 1` primes.** There is an absolute constant
`C` such that for every natural number `m ≥ 1`, `p_{n+m} - p_n ≤ C m³ e^{4m}` for infinitely
many `n`, that is `lim inf_n (p_{n+m} - p_n) ≪ m³ e^{4m}` (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Theorem 1.1). -/
theorem_wanted frequently_nth_prime_add_sub_le_cube_mul_exp :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∃ᶠ n in atTop,
      ((Nat.nth Nat.Prime (n + m) - Nat.nth Nat.Prime n : ℕ) : ℝ) ≤
        C * (m : ℝ) ^ 3 * Real.exp (4 * m)

/-- **A positive proportion of `m`-subsets satisfy the prime `m`-tuples conjecture.** For every
natural number `m ≥ 1` there are `c > 0` and `r₀` such that for every set `A` of `r ≥ r₀` distinct
integers, at least `c · C(r, m)` of the `m`-element subsets `B ⊆ A` have infinitely many integers
`n` with `n + b` prime for every `b ∈ B` (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Theorem 1.2). Primality of `n + b` is that of the natural number
`(n + b).toNat`, so negative values are not prime. -/
theorem_wanted exists_pos_mul_choose_le_ncard_prime_translates (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, ∀ A : Finset ℤ, r₀ ≤ A.card →
      c * (A.card.choose m : ℝ) ≤
        ({B : Finset ℤ | B ⊆ A ∧ B.card = m ∧
          {n : ℤ | ∀ b ∈ B, (n + b).toNat.Prime}.Infinite} : Set (Finset ℤ)).ncard

/-- **Three primes in intervals of length 600 under Elliott–Halberstam.** If the primes have
level of distribution `θ` for every `θ < 1` (dyadic Elliott–Halberstam), then
`p_{n+2} - p_n ≤ 600` for infinitely many `n` (Maynard, *Small gaps between primes*,
arXiv:1311.4600v3, Theorem 1.4, second inequality). -/
theorem_wanted elliottHalberstam_frequently_nth_prime_add_two_sub_le_600 :
    ElliottHalberstam → ∃ᶠ n in atTop, Nat.nth Nat.Prime (n + 2) - Nat.nth Nat.Prime n ≤ 600

/-- **GPY: level beyond `1/2` gives two primes in long admissible tuples.** For every `ϑ > 1/2`
there is `k₀` such that, if the primes have level of distribution `ϑ`, every admissible set `H` of
at least `k₀` non-negative integers has infinitely many `n` with at least two of the `n + h`,
`h ∈ H`, prime (Goldston, Pintz and Yıldırım, *Primes in tuples I*, arXiv:math/0508185v1,
Theorem 1, first sentence). The source's `C(ϑ)` is explicitly calculable; that is not
recorded. -/
theorem_wanted exists_card_two_le_primeShiftCount_of_level_gt_half (ϑ : ℝ) (hϑ : 1 / 2 < ϑ) :
    ∃ k₀ : ℕ, (∀ θ : ℝ, 0 < θ → θ < ϑ → ElliottHalberstamAt θ) →
      ∀ H : Finset ℕ, MetaMathlibExt.IsAdmissibleFinset (H.image fun h : ℕ => (h : ℤ)) →
        k₀ ≤ H.card → {n : ℕ | 2 ≤ primeShiftCount H n}.Infinite

/-- **GPY: level `0.971` gives two primes in every admissible 6-tuple.** If the primes have level
of distribution `ϑ ≥ 0.971`, then every admissible set `H` of at least 6 non-negative integers has
infinitely many `n` with at least two of the `n + h`, `h ∈ H`, prime (Goldston, Pintz and
Yıldırım, *Primes in tuples I*, arXiv:math/0508185v1, Theorem 1, second sentence). With the
admissible 6-tuple `{0, 4, 6, 10, 12, 16}` this gives `lim inf (p_{n+1} - p_n) ≤ 16` (GPY (1.7)),
the conditional bound recorded as `PrimeGapBounds.gpyElliottHalberstamUpperBound`. -/
theorem_wanted two_le_primeShiftCount_infinite_of_level_ge (ϑ : ℝ) (hϑ : 0.971 ≤ ϑ)
    (hlevel : ∀ θ : ℝ, 0 < θ → θ < ϑ → ElliottHalberstamAt θ) (H : Finset ℕ)
    (hH : MetaMathlibExt.IsAdmissibleFinset (H.image fun h : ℕ => (h : ℤ))) (hk : 6 ≤ H.card) :
    {n : ℕ | 2 ≤ primeShiftCount H n}.Infinite

end WantedExt.NumberTheory.MaynardSmallGaps
