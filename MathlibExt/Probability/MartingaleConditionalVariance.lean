/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Martingale.Basic

/-!
# Conditional variance of a square-integrable martingale increment

If `X` is a square-integrable martingale with respect to the filtration `ℱ`,
then for `m ≤ n`,
`E[(X_n - X_m)^2 | ℱ_m] = E[X_n^2 | ℱ_m] - X_m^2` almost surely. This is the
conditional variance of the increment `X_n - X_m`, expressed through the
conditional second moment of `X_n`.

## Source

This formalizes the target "Theorem (Conditional variance theorem)"
(Lecture 28) of `v1/Atlas/TheoryOfProbability/targets.yaml`, whose v1
formalization is `v1/Atlas/TheoryOfProbability/code/ConditionalVariance.lean`
(`martingale_condVar_identity`). The companion definition-only
restatement of the ordinary conditional-variance formula in that v1 file is
not ported: it is just Mathlib's
`ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`.

## Main results

* `MeasureTheory.Martingale.condExp_sub_sq_eq`: the conditional variance
  identity for martingale increments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace MeasureTheory

/-- **Conditional variance theorem for martingales** (Lecture 28).

If `X` is a square-integrable martingale with respect to the filtration `ℱ`,
then for `m ≤ n`,
`E[(X_n - X_m)^2 | ℱ_m] = E[X_n^2 | ℱ_m] - X_m^2` almost surely.

This expresses the conditional variance of the increment `X_n - X_m` in
terms of the conditional second moment of `X_n`. -/
theorem Martingale.condExp_sub_sq_eq
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    (hL2 : ∀ n, MemLp (X n) 2 μ)
    {m n : ℕ} (hmn : m ≤ n) :
    μ[fun ω => (X n ω - X m ω) ^ 2 | ℱ m] =ᵐ[μ]
      fun ω => (μ[fun ω' => (X n ω') ^ 2 | ℱ m]) ω - (X m ω) ^ 2 := by
  have hcond : μ[X n | ↑(ℱ m)] =ᵐ[μ] X m := hmart.condExp_ae_eq hmn
  have hfun_ae : (fun ω => (X n ω - X m ω) ^ 2) =ᵐ[μ]
      (fun ω => (X n ω - (μ[X n | ℱ m]) ω) ^ 2) := by
    filter_upwards [hcond] with ω hω
    rw [hω]
  have step3 : μ[fun ω => (X n ω - X m ω) ^ 2 | ℱ m] =ᵐ[μ]
      condVar (ℱ m) (X n) μ :=
    condExp_congr_ae (m := ↑(ℱ m)) hfun_ae
  have step4 : condVar (ℱ m) (X n) μ =ᵐ[μ]
      μ[X n ^ 2 | ℱ m] - μ[X n | ℱ m] ^ 2 :=
    condVar_ae_eq_condExp_sq_sub_sq_condExp (ℱ.le m) (hL2 n)
  have step5 : (fun ω => (μ[X n | ℱ m]) ω ^ 2) =ᵐ[μ]
      (fun ω => (X m ω) ^ 2) := by
    filter_upwards [hcond] with ω hω
    rw [hω]
  have hpow : X n ^ 2 = fun ω' => X n ω' ^ 2 := by ext; simp [Pi.pow_apply]
  filter_upwards [step3, step4, step5] with ω h3 h4 h5
  rw [h3, h4]
  simp only [Pi.sub_apply, Pi.pow_apply]
  rw [h5, hpow]

end MeasureTheory
