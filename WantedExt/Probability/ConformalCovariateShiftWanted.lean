/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.WeightedConformal
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Weighted split conformal prediction under covariate shift

Under covariate shift the training pairs `(Xᵢ, Yᵢ)`, `i = 1, …, n`, are i.i.d. from
`P = P_X × P_{Y|X}` and the test pair `(X_{n+1}, Y_{n+1})` is drawn independently from
`P̃ = P̃_X × P_{Y|X}`: only the covariate law changes. If `P̃_X ≪ P_X` with likelihood ratio
`w = dP̃_X / dP_X`, reweighting the empirical distribution of the scores by
`pᵢ(x) = w(Xᵢ) / (∑ⱼ w(Xⱼ) + w(x))`, with the remaining mass `p_{n+1}(x)` at `+∞`, restores the
`1 - α` coverage guarantee (R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas,
*Conformal prediction under covariate shift*, NeurIPS 2019, arXiv:1904.06019, Corollary 1). The
proof, through weighted exchangeability (Lemma 3 and Theorem 2 there), is deferred.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.WeightedConformal

namespace MathlibExt.Probability.ConformalCovariateShiftWanted

/-- **Weighted split conformal coverage under covariate shift.** Let `P_X`, `P̃_X` be probability
measures on the covariate space with `P̃_X ≪ P_X`, let `κ` be a Markov kernel giving the
conditional law of the response, and let `w` be the Radon-Nikodym derivative `dP̃_X / dP_X`.
Let the data `D = ((X₁, Y₁), …, (Xₙ, Yₙ); (X_{n+1}, Y_{n+1}))` have law
`(P_X ⊗ κ)^{⊗ n} ⊗ (P̃_X ⊗ κ)`, and let `s` be a measurable score function. For `0 < α < 1`, the
test score `s(X_{n+1}, Y_{n+1})` is at most the level-`(1 - α)` quantile of
`∑ᵢ pᵢ δ_{s(Xᵢ, Yᵢ)} + p_{n+1} δ_{+∞}`, with `pᵢ = w(Xᵢ) / (∑ⱼ w(Xⱼ) + w(X_{n+1}))`, with
probability at least `1 - α`.

Source: R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under
covariate shift*, NeurIPS 2019, arXiv:1904.06019, Corollary 1, for a score function that does not
depend on the data bag, `S((x, y), Z) = s(x, y)`; this is the weighted split conformal case of
their Section 2.2, which uses `s(x, y) = |y - μ₀(x)|` for a regression function `μ₀` fitted on
independent data (the statement is conditional on that fit). The event is `Y_{n+1} ∈ Ĉₙ(X_{n+1})`
for the band `Ĉₙ(x) = {y : s(x, y) ≤ Quantile(1 - α; ∑ᵢ pᵢ(x) δ_{Vᵢ} + p_{n+1}(x) δ_∞)}`. -/
theorem_wanted le_measure_score_le_weightedQuantile {𝒳 : Type*} [MeasurableSpace 𝒳]
    (PX PtX : Measure 𝒳) [IsProbabilityMeasure PX] [IsProbabilityMeasure PtX] (hac : PtX ≪ PX)
    (κ : Kernel 𝒳 ℝ) [IsMarkovKernel κ] {s : 𝒳 × ℝ → ℝ} (hs : Measurable s) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ENNReal.ofReal (1 - α) ≤
      ((Measure.pi fun _ : Fin n => PX ⊗ₘ κ).prod (PtX ⊗ₘ κ))
        {D | (s D.2 : WithTop ℝ) ≤ weightedQuantile (1 - α) (fun i => s (D.1 i))
          (fun i => (PtX.rnDeriv PX (D.1 i).1).toReal /
            (∑ j, (PtX.rnDeriv PX (D.1 j).1).toReal + (PtX.rnDeriv PX D.2.1).toReal))}

end MathlibExt.Probability.ConformalCovariateShiftWanted
