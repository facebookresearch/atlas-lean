/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A real zero of p or of G₁ in even degree (Shapiro, Conjecture 12)

B. Shapiro, Problems around polynomials, Conjecture 12: for any real polynomial `p(x)` of even
degree `k`, `#_r[(k - 1)(p′(x))² - k p(x) p″(x)] + #_r p(x) > 0` (`#_r`: number of real zeros).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.Algebra.EvenDegreeWeightedLaguerreRealZeroAMR21Problem0019Wanted

/-!
Source: B. Shapiro, Problems around polynomials: the good, the bad and the ugly..., Arnold Math. J.
1 (2015), arXiv:1503.05295, Conjecture 12 (B. Shapiro). UnsolvedMath record UM-02200019
(`AMR-021-0019`), dataset ulamai/UnsolvedMath v1.8.0.

Even degree `k ≥ 4`. In degree 2 the statement fails for a trivial reason: for `p = x² + bx + c`
with `b² < 4c`, `G₁ = (2x + b)² - 4p = b² - 4c` is a negative constant, so neither `p` nor `G₁` has
a real zero (e.g. `p = x² + 1`, `G₁ = -4`); the conjecture rests on experiments up to degree 6, and
its refutation by Katkova–Tyaglov–Vishnyakova (who state it for even `n ≥ 2`) is in every even
degree `n ≥ 4`, so the target is that range. Real zeros are counted with multiplicity (`roots`); the
counterexample has no real zeros at all.
-/

open Polynomial

/-- Shapiro's Conjecture 12, in even degree `k ≥ 4` (degree `2` fails trivially): the polynomial
`G₁ = (k - 1) (p')² - k p p''` and `p` together have a real zero, i.e. the numbers of real zeros
of `G₁` and of `p` (counted with multiplicity) have a positive sum. -/
def evenDegreeWeightedLaguerreRealZero : Prop :=
  ∀ p : ℝ[X], 4 ≤ p.natDegree → Even p.natDegree →
    0 < Multiset.card (((p.natDegree : ℝ) - 1) • derivative p ^ 2 -
        (p.natDegree : ℝ) • (p * derivative (derivative p))).roots + Multiset.card p.roots

/--
Resolved false: Katkova, Tyaglov and Vishnyakova show that `p(x) = x^{2n}/(2n) + x²/2 + 1` (`n ≥ 2`,
degree `2n`) has no real zeros and that `(2n - 1)(p′)² - 2n p p″` has no real zeros either; for `n =
2` this is `-x⁴ - 11x² - 4`. Source: B. Shapiro, Problems around polynomials: the good, the bad and
the ugly..., Arnold Math. J. 1 (2015), arXiv:1503.05295, Conjecture 12 (B. Shapiro); resolution: O.
Katkova, M. Tyaglov and A. Vishnyakova, Some generalizations of the Hawaii conjecture and beyond,
Complex Anal. Oper. Theory 19 (2025), DOI 10.1007/s11785-025-01664-z, arXiv:2406.00686, Proposition
2.11 and §3: for n ≥ 2, p_{2n}(x) = x^{2n}/(2n) + x²/2 + 1 has Z_R(p) = 0 and -2n
H_{(2n-1)/(2n)}[p](x) = x^{2n}(2n² - 5n + 3) + 2n(2n - 1)x^{2n-2} - (n - 1)x² + 2n has no real
zeros, so Z_R((2n - 1)(p′)² - 2n p p″) + Z_R(p) = 0 for every even degree 2n ≥ 4,
https://doi.org/10.1007/s11785-025-01664-z.
-/
public theorem_wanted evenDegreeWeightedLaguerreRealZero_refuted :
    ¬ evenDegreeWeightedLaguerreRealZero

end MathlibExt.Algebra.EvenDegreeWeightedLaguerreRealZeroAMR21Problem0019Wanted
