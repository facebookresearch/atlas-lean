/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.GlivenkoCantelli
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant

For an i.i.d. sample of size `N` from a distribution function `F` on `ℝ`, with empirical
distribution function `F_N`, the Dvoretzky–Kiefer–Wolfowitz inequality bounds the probability
that `F_N` is uniformly `ε`-far from `F`:

`P(sup_x |F_N(x) - F(x)| > ε) ≤ C exp(-2 N ε²)` for every `ε > 0`.

Dvoretzky, Kiefer and Wolfowitz (Ann. Math. Statist. 27 (1956) 642–669) proved it with an
unspecified constant `C`. Massart (Ann. Probab. 18 (1990) 1269–1283), Theorem 1, as stated on
p. 2 of Reeve, arXiv:2403.16651v1 (the source read for this entry; Massart's paper was not),
gives the one-sided bound `P(sup_x √N (F_N(x) - F(x)) > λ) ≤ exp(-2 λ²)` for
`λ ≥ min {√(log 2 / 2), 1.0841 N^(-1/6)}`. Reeve's Corollary 2 gives the one-sided bound
`exp(-2 λ²)` for every `λ ≥ 0`, for independent observations with an arbitrary distribution
function `F`.

The two-sided bound `2 exp(-2 N ε²)` stated here follows by a union bound. The upper deviation is
the bound above with `λ = √N ε`. The lower deviation `sup_x (F(x) - F_N(x))` is at most the upper
deviation of the sample `-X_i` (compare left limits), so it obeys the same bound. When
`√N ε < √(log 2 / 2)` the right-hand side exceeds `1` and there is nothing to prove, so
Massart's Theorem 1 alone already covers every `ε > 0`. The inequality is used in this form,
`2 exp(-2 n ε²)`, in the proof of Theorem 2.4 of Lei, G'Sell, Rinaldo, Tibshirani and Wasserman,
arXiv:1604.04173v2, Appendix A.1.

The empirical count is the one of the Glivenko–Cantelli theorem in this library
(`MathlibExt.Probability.Statistics.GlivenkoCantelliWanted.empiricalCount`), which counts the
indices `0, …, n`; the sample size is therefore `N = n + 1`, which also excludes the empty
sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GlivenkoCantelliWanted

namespace MathlibExt.Probability.Statistics.DKWInequalityWanted

/-- **Dvoretzky–Kiefer–Wolfowitz inequality with Massart's constant.** Let `X₀, X₁, …` be
independent real random variables on a probability space, each with the law of `X₀`, and let
`F(x) = P(X₀ ≤ x)`. For every `n` and every `ε > 0`, the empirical distribution function
`F_{n+1}(x) = #{i ≤ n : X_i ≤ x} / (n + 1)` of the first `n + 1` observations satisfies
`P(∃ x, |F_{n+1}(x) - F(x)| > ε) ≤ 2 exp(-2 (n + 1) ε²)`. This is the two-sided form of
P. Massart, *The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality*, Ann. Probab. 18
(1990) 1269–1283, Theorem 1 (a one-sided bound, as stated in H. W. J. Reeve, arXiv:2403.16651v1,
p. 2), obtained by a union bound over the two deviations. Reeve's Corollary 2 gives the one-sided
bound for an arbitrary distribution function `F` and every level. The constant is unspecified in
A. Dvoretzky, J. Kiefer and J. Wolfowitz, Ann. Math. Statist. 27 (1956) 642–669. -/
theorem_wanted measure_exists_abs_empiricalCDF_sub_gt_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hMeas : ∀ n, Measurable (X n))
    (hIndep : iIndepFun X P) (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    P {ω | ∃ x : ℝ, ε < |(empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) -
        (P (X 0 ⁻¹' Set.Iic x)).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ((n + 1 : ℕ) : ℝ) * ε ^ 2))

end MathlibExt.Probability.Statistics.DKWInequalityWanted
