/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Explicit bounds on the Zhang--Zagier essential minimum
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Height.ZhangZagier

@[expose] public section

namespace MathlibExt.NumberTheory.Height

/-!
# Explicit bounds on the Zhang--Zagier essential minimum

The established bounds in teorth/optimizationproblems `constants/82a.md` are recorded as wishlist
theorems pending Lean proofs. Decimal notation in these statements denotes exact rational real
numbers. The source's comments about algorithms converging to the constant and the comparison with
stable Faltings height are background, not additional bound claims.
-/

/-- Dresden's 2003 upper bound.

Source: Gregory P. Dresden, “Sums of heights of algebraic numbers,” Math. Comp. 72 (2003),
no. 243, 1487–1499, Section 7; also recorded in teorth/optimizationproblems,
`constants/82a.md`.
-/
public theorem_wanted zhangZagierEssentialMinimum_le_dresden2003 :
    zhangZagierEssentialMinimum ≤ 0.39679

/-- Doche's 2001 upper bound from *On the spectrum of the Zhang-Zagier height*.

Source: Christophe Doche, “On the spectrum of the Zhang-Zagier height,” Math. Comp. 70
(2001), no. 233, 419–430; also recorded in teorth/optimizationproblems,
`constants/82a.md`.
-/
public theorem_wanted zhangZagierEssentialMinimum_le_doche2001Spectrum :
    zhangZagierEssentialMinimum ≤ 0.25594

/-- Doche's 2001 upper bound from *Zhang-Zagier heights of perturbed polynomials*.

Source: Christophe Doche, “Zhang-Zagier heights of perturbed polynomials,” J. Théor.
Nombres Bordeaux 13 (2001), no. 1, 103–110; also recorded in
teorth/optimizationproblems, `constants/82a.md`.
-/
public theorem_wanted zhangZagierEssentialMinimum_le_doche2001Perturbed :
    zhangZagierEssentialMinimum ≤ 0.25444

/-- Grinsztajn's 2026 computation-based upper bound.

Source: Max Grinsztajn, “Code and certification data for an improved C82 Zhang-Zagier
bound,” GitHub repository (2026),
<https://github.com/maaxgrin/zhang-zagier-c82-bound>; also recorded in
teorth/optimizationproblems, `constants/82a.md`.
-/
public theorem_wanted zhangZagierEssentialMinimum_le_grinsztajn2026 :
    zhangZagierEssentialMinimum ≤ 0.2536331090204145

/-- Zhang's 1995 strict positivity result.

Source: Shouwu Zhang, “Positive line bundles on arithmetic varieties,” J. Amer. Math.
Soc. 8 (1995), no. 1, 187–221; also recorded in teorth/optimizationproblems,
`constants/82a.md`.
-/
public theorem_wanted zhangZagierEssentialMinimum_pos :
    0 < zhangZagierEssentialMinimum

/-- Zagier's 1993 exact symbolic lower bound.

Source: Don Zagier, “Algebraic numbers close to both 0 and 1,” Math. Comp. 61 (1993),
no. 203, 485–491; also recorded in teorth/optimizationproblems, `constants/82a.md`.
-/
public theorem_wanted zagier1993_le_zhangZagierEssentialMinimum :
    (1 / 2 : ℝ) * Real.log ((1 + Real.sqrt 5) / 2) ≤ zhangZagierEssentialMinimum

/-- Doche's 2001 lower bound from *On the spectrum of the Zhang-Zagier height*.

Source: Christophe Doche, “On the spectrum of the Zhang-Zagier height,” Math. Comp. 70
(2001), no. 233, 419–430; also recorded in teorth/optimizationproblems,
`constants/82a.md`.
-/
public theorem_wanted doche2001_le_zhangZagierEssentialMinimum :
    0.24824 ≤ zhangZagierEssentialMinimum

/-- Flammang's 2018 lower bound, the best lower row in the frozen source.

Source: Véronique Flammang, “On the Zhang-Zagier measure,” Int. J. Number Theory 14
(2018), no. 10, 2663–2671; also recorded in teorth/optimizationproblems,
`constants/82a.md`.
-/
public theorem_wanted flammang2018_le_zhangZagierEssentialMinimum :
    0.24874 ≤ zhangZagierEssentialMinimum

end MathlibExt.NumberTheory.Height
