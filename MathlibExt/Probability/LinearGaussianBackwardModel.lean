/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Linear Gaussian additive noise models are reversible

In the structural equation `Y = φ X + N` with the noise `N` independent of the cause `X`, if
`X` and `N` are Gaussian there is a *backward* model `X = ψ Y + Ñ` with `Ñ` independent of `Y`:
the joint law of `(X, Y)` does not reveal the causal direction. This is the "if" direction of
the characterization of reversible linear additive noise models (Peters, Mooij, Janzing and
Schölkopf, Proposition 13, after Shimizu et al. 2006). The "only if" direction is proved in
`MathlibExt.Probability.LinearNonGaussianIdentifiability`.

The coefficient is the regression coefficient `ψ = Cov(X, Y) / Var(Y)`: `(X - ψ Y, Y)` is a
linear image of the jointly Gaussian pair `(X, N)`, hence jointly Gaussian, and its two
coordinates are uncorrelated, hence independent.

## Main results

* `exists_indepFun_backward_of_hasGaussianLaw`: independent Gaussian `X`, `N` (possibly
  degenerate) have a backward model, for every `φ`.
* `exists_indepFun_backward_of_map_eq_gaussianReal`: the same with the laws written as
  `gaussianReal m v`.

## References

* J. Peters, J. M. Mooij, D. Janzing and B. Schölkopf, "Causal discovery with continuous additive
  noise models", *J. Mach. Learn. Res.* **15** (2014), 2009–2053, Example 12 and Proposition 13.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.LinearGaussianBackwardModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X N : Ω → ℝ}

/-- **A linear Gaussian additive noise model has a backward model** (Peters, Mooij, Janzing and
Schölkopf, *Causal discovery with continuous additive noise models*, JMLR 15 (2014),
Example 12 and the "if" direction of Proposition 13). Let `X` and `N` be independent random
variables with Gaussian laws (possibly degenerate) and let `Y = φ X + N`. Then there is `ψ ∈ ℝ`
such that `Ñ = X - ψ Y` is independent of `Y`; one can take `ψ = Cov(X, Y) / Var(Y)`. -/
theorem exists_indepFun_backward_of_hasGaussianLaw (hX : HasGaussianLaw X P)
    (hN : HasGaussianLaw N P) (hXN : IndepFun X N P) (φ : ℝ) :
    ∃ ψ : ℝ, IndepFun (fun ω => X ω - ψ * (φ * X ω + N ω)) (fun ω => φ * X ω + N ω) P := by
  have hP := hX.isProbabilityMeasure
  have hXN2 := IndepFun.hasGaussianLaw hX hN hXN
  have hX2 : MemLp X 2 P := hX.memLp_two
  have hN2 : MemLp N 2 P := hN.memLp_two
  set Y : Ω → ℝ := fun ω => φ * X ω + N ω with hYdef
  have hφX : MemLp (fun ω => φ * X ω) 2 P := hX2.const_mul φ
  have hY2 : MemLp Y 2 P := hφX.add hN2
  have hYeq : Y = (fun ω => φ * X ω) + N := rfl
  have hcovXN : cov[X, N; P] = 0 := hXN.covariance_eq_zero hX2 hN2
  have hcovNX : cov[N, X; P] = 0 := by rw [covariance_comm, hcovXN]
  have hcovXY : cov[X, Y; P] = φ * Var[X; P] := by
    rw [hYeq, covariance_add_right hX2 hφX hN2, covariance_const_mul_right, hcovXN,
      covariance_self hX2.aemeasurable, add_zero]
  have hcovYY : cov[Y, Y; P] = φ ^ 2 * Var[X; P] + Var[N; P] := by
    rw [hYeq, covariance_add_left hφX hN2 (hφX.add hN2), covariance_add_right hφX hφX hN2,
      covariance_add_right hN2 hφX hN2, covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_mul_right, covariance_const_mul_left, hcovXN, hcovNX,
      covariance_self hX2.aemeasurable, covariance_self hN2.aemeasurable]
    ring
  set ψ : ℝ := cov[X, Y; P] / cov[Y, Y; P]
  refine ⟨ψ, ?_⟩
  have hG : HasGaussianLaw (fun ω => (X ω - ψ * Y ω, Y ω)) P := by
    let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ - ψ • (φ • ContinuousLinearMap.fst ℝ ℝ ℝ +
        ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
        (φ • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
    have h := hXN2.map L
    convert h using 1
    funext ω
    simp [L, Y, smul_eq_mul]
    ring
  refine hG.indepFun_of_covariance_eq_zero ?_
  rw [covariance_fun_sub_left hX2 (hY2.const_mul ψ) hY2, covariance_const_mul_left]
  by_cases h : cov[Y, Y; P] = 0
  · have hvX := variance_nonneg X P
    have hvN := variance_nonneg N P
    have h1 : φ ^ 2 * Var[X; P] = 0 := by nlinarith [sq_nonneg φ, mul_nonneg (sq_nonneg φ) hvX]
    have h2 : φ * Var[X; P] = 0 := by
      rcases mul_eq_zero.1 h1 with h3 | h3
      · simp [pow_eq_zero_iff two_ne_zero |>.1 h3]
      · simp [h3]
    rw [h, hcovXY, h2]
    ring
  · simp only [ψ]
    field_simp
    ring

/-- **Linear additive noise models with Gaussian laws are reversible**, the laws being written
as `gaussianReal` (Peters, Mooij, Janzing and Schölkopf, *Causal discovery with continuous
additive noise models*, JMLR 15 (2014), the "if" direction of Proposition 13). If `X` and `N`
are independent and measurable with `X ~ 𝒩(m₁, v₁)` and `N ~ 𝒩(m₂, v₂)`, then for every `φ`
there is `ψ` such that `X - ψ (φ X + N)` is independent of `φ X + N`. -/
theorem exists_indepFun_backward_of_map_eq_gaussianReal [IsProbabilityMeasure P]
    (hXm : Measurable X) (hNm : Measurable N) (hXN : IndepFun X N P) {m₁ m₂ : ℝ}
    {v₁ v₂ : NNReal} (hXlaw : P.map X = gaussianReal m₁ v₁) (hNlaw : P.map N = gaussianReal m₂ v₂)
    (φ : ℝ) :
    ∃ ψ : ℝ, IndepFun (fun ω => X ω - ψ * (φ * X ω + N ω)) (fun ω => φ * X ω + N ω) P := by
  have hX : HasGaussianLaw X P := by
    have : IsGaussian (P.map X) := by rw [hXlaw]; infer_instance
    exact IsGaussian.hasGaussianLaw hXm.aemeasurable
  have hN : HasGaussianLaw N P := by
    have : IsGaussian (P.map N) := by rw [hNlaw]; infer_instance
    exact IsGaussian.hasGaussianLaw hNm.aemeasurable
  exact exists_indepFun_backward_of_hasGaussianLaw hX hN hXN φ

end MathlibExt.Probability.LinearGaussianBackwardModel
