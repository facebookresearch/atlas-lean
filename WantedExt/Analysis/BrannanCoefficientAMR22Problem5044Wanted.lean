/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Brannan's coefficient conjecture for β = 1 (Hayman–Lingham Problem 5.44)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 5.44 (D. A. Brannan):
for `0 < α < 1` and `|x| = 1` let `(1 + xz)^α / (1 - z) = ∑ A_n(x) zⁿ`. Is `|A_{2n+1}(x)| ≤
|A_{2n+1}(1)|` for `n ≥ 2`? It is true for `n = 1` and false for every even index; more generally
one can ask the same for the coefficients of `(1 + xz)^α (1 - z)^{-β}`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.Polynomial.Pochhammer

@[expose] public section

namespace MathlibExt.Analysis.BrannanCoefficientAMR22Problem5044Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 5.44 (D. A. Brannan). UnsolvedMath record UM-02305044
(`AMR-022-5044`), dataset ulamai/UnsolvedMath v1.8.0.

`A_n(x)` is the coefficient of `zⁿ` in the product of `(1 + xz)^α = ∑ binom(α, j) x^j z^j` and
`1/(1-z) = ∑ z^j`, i.e. `∑_{j=0}^{n} binom(α, j) x^j` with `binom(α, j) = α(α-1)⋯(α-j+1)/j!`
(`descPochhammer`). The target covers every odd index `2n + 1 ≥ 3`, including the known case `n =
1`. The general question for `(1 + xz)^α (1 - z)^{-β}` is not formalized.
-/

/-- The coefficient `A_n(x)` of `zⁿ` in `(1 + x z)^α / (1 - z) = ∑ A_n(x) zⁿ`:
`A_n(x) = ∑_{j=0}^{n} binom(α, j) x^j`, with `binom(α, j) = α (α - 1) ⋯ (α - j + 1) / j!`. -/
noncomputable def brannanCoeff (α : ℝ) (x : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1), (((descPochhammer ℝ j).eval α / j.factorial : ℝ) : ℂ) * x ^ j

/-- Brannan's conjecture for `β = 1` (Hayman–Lingham Problem 5.44): for `0 < α < 1`, `|x| = 1`
and every `n ≥ 1`, `|A_{2n+1}(x)| ≤ |A_{2n+1}(1)|`. -/
def brannanOddCoefficientBound : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → ∀ x : ℂ, ‖x‖ = 1 → ∀ n : ℕ, 1 ≤ n →
    ‖brannanCoeff α x (2 * n + 1)‖ ≤ ‖brannanCoeff α 1 (2 * n + 1)‖

/--
Resolved true: Brannan's conjecture for `β = 1` holds for every odd index (Barnard and Richards,
after the aggregate proof of Jayatilake, Szász and Deniz–Çağlar–Szász), so `|A_{2n+1}(x)| ≤
|A_{2n+1}(1)|` for `0 < α < 1`, `|x| = 1` and all `n ≥ 1`. Source: W. K. Hayman and E. F. Lingham,
Research Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem
5.44 (D. A. Brannan); resolution: R. W. Barnard and K. C. Richards, A direct proof of Brannan's
conjecture for β = 1, J. Math. Anal. Appl. 493 (2021), 124534, DOI 10.1016/j.jmaa.2020.124534;
earlier aggregate proof: U. C. Jayatilake, Complex Var. Elliptic Equ. 58 (2013) 685-694 (odd n ≤
51), R. Szász, Mediterr. J. Math. 17 (2020) 38, and E. Deniz, M. Çağlar and R. Szász, The final step
in a proof of Brannan's conjecture for β = 1, J. Math. Anal. Appl. 487 (2020) 124001, as summarized
in T. M. Dunster, The general Brannan coefficient conjecture I: Watson-lemma approximations, Anal.
Appl. (2026), DOI 10.1142/S0219530526500636, arXiv:2602.15308, abstract and §1: for β = 1 and α ∈
(0, 1) the conjecture 'has recently been proven for all odd integers n ≥ 5 by a number of authors in
aggregate', and Barnard and Richards 'provided a fully direct analytic proof for β = 1 valid for all
positive odd n', https://doi.org/10.1016/j.jmaa.2020.124534.
-/
public theorem_wanted brannanOddCoefficientBound_holds : brannanOddCoefficientBound

end MathlibExt.Analysis.BrannanCoefficientAMR22Problem5044Wanted
