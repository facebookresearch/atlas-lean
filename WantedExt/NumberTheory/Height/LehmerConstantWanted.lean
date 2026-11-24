/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Height.LehmerConstant

@[expose] public section

namespace MathlibExt.NumberTheory.LehmerConstant

open Polynomial

/-!
# Catalogue bounds for Lehmer's Mahler measure constant

The frozen catalogue bounds for constant C40a, Lehmer's constant
`L = inf {M(f) | f ∈ ℤ[X], 1 < M(f)}`, as proof requests against
`lehmerConstant` and `intMahlerMeasure` from the provider.

The provider proves the elementary bounds `1 ≤ L ≤ 2` (the catalogue's
trivial lower row `1`, and the witness `M(X - 2) = 2`) and the equivalence
of `L = 1` with Lehmer's question. The requests below are the sharp
catalogue upper bound given by Lehmer's example polynomial, whose Mahler
measure `1.176280818...` is the smallest known value larger than `1`, and
Smyth's theorem for nonreciprocal polynomials from the catalogue's
additional comments. Decimal bounds are exact rationals rounding the
catalogue's displayed digits in the safe direction.
-/

/-- **Mahler measure of Lehmer's polynomial.** The Mahler measure of Lehmer's polynomial is at most
$1176281/1000000 = 1.176281$.

Source: Lehmer (1933), the Mahler measure of Lehmer's polynomial is
`1.176280818...`, hence at most `1.176281`. No root-location computation
for the degree-ten example is formalized here. -/
theorem_wanted intMahlerMeasure_lehmerPolynomial_le :
    intMahlerMeasure lehmerPolynomial ≤ 1176281 / 1000000

/-- **Lehmer's upper bound for Lehmer's constant.** Lehmer's constant is at most
$1176281/1000000 = 1.176281$.

Source: Lehmer (1933), catalogue upper bound `C₄₀ₐ ≤ 1.176280...`
from the Mahler measure of Lehmer's polynomial, rounded up at the sixth
decimal place. -/
theorem_wanted lehmer1933UpperBound_wanted :
    lehmerConstant ≤ 1176281 / 1000000

/-- **Smyth's theorem for nonreciprocal polynomials.** Let $f \in \mathbb{Z}[X]$ be an integer
polynomial that is not reciprocal and whose constant term $f(0)$ is nonzero. Then the Mahler
measure of $f$ is at least the Mahler measure of Smyth's polynomial $X^3 - X - 1$.

Source: Smyth (1971), as quoted in the catalogue: a nonreciprocal
integer polynomial with nonzero constant term has Mahler measure at
least that of `X^3 - X - 1` (the plastic number `1.324717...`). -/
theorem_wanted smyth1971Nonreciprocal_wanted (f : Polynomial ℤ)
    (hf : ¬ IsReciprocal f) (hf0 : Polynomial.eval 0 f ≠ 0) :
    intMahlerMeasure smythPolynomial ≤ intMahlerMeasure f

end MathlibExt.NumberTheory.LehmerConstant
