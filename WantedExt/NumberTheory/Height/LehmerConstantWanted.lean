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
# Catalogue bound for nonreciprocal polynomials

For Lehmer's constant `L`, the provider proves the elementary bounds `1 ≤ L ≤ 2`
and the sharper upper bound `L ≤ 1176281/1000000` witnessed by Lehmer's polynomial.
The remaining request is Smyth's theorem from the catalogue's additional comments.
-/

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
