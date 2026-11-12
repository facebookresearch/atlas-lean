/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Two-group Oaxaca–Blinder decomposition

Under the coefficient convention that each group's mean outcome equals its mean regressor
vector times its own coefficients, with group `B` as the reference, the mean outcome gap
splits into an explained part (differences in characteristics, valued at `B`'s coefficients)
and a coefficient part (differences in coefficients, at `A`'s characteristics):

`ȳ_A - ȳ_B = (x̄_A - x̄_B) ⬝ β_B + x̄_A ⬝ (β_A - β_B)` (`meanGap_eq`).

For least-squares fits with an intercept the convention holds: the normal equations
`Xᵀ X β = Xᵀ y` at the intercept coordinate say the residuals sum to zero
(`sampleMean_eq_regressorMean_dotProduct`), so the decomposition reconstructs the observed gap
of OLS fits (`sampleMean_sub_eq`). The normal equations are stated in the form used by
`Cslib.MachineLearning.LeastSquares`. The decomposition is an accounting identity, not a
causal discrimination estimate.

## Main results

* `MathlibExt.Economics.OaxacaBlinder.meanGap_eq`
* `MathlibExt.Economics.OaxacaBlinder.sampleMean_eq_regressorMean_dotProduct`
* `MathlibExt.Economics.OaxacaBlinder.sampleMean_sub_eq`

Atlas roadmap target AP04.T03.
-/

namespace MathlibExt.Economics.OaxacaBlinder

open Matrix MathlibExt.Probability.FiniteProbability

/-- Average regressor vector: the column means of the `n × κ` regressor matrix `X`, each the
`sampleMean` of that column. -/
noncomputable def regressorMean {n : ℕ} {κ : Type*} (X : Matrix (Fin n) κ ℝ) : κ → ℝ :=
  fun j => sampleMean (fun i => X i j)

/-- **Two-group Oaxaca–Blinder decomposition.** Coefficient convention: each group's mean
outcome equals its mean regressor vector times its own coefficient vector
(`ȳ_A = x̄_A ⬝ β_A`, `ȳ_B = x̄_B ⬝ β_B`), and group `B`'s coefficients are the reference. Then
the mean gap splits into the part explained by characteristics, `(x̄_A - x̄_B) ⬝ β_B`, and the
part due to coefficients, `x̄_A ⬝ (β_A - β_B)`. This is an accounting identity, not a causal
discrimination estimate. -/
theorem meanGap_eq {κ : Type*} [Fintype κ] {xA xB βA βB : κ → ℝ} {yA yB : ℝ}
    (hA : yA = xA ⬝ᵥ βA) (hB : yB = xB ⬝ᵥ βB) :
    yA - yB = (xA - xB) ⬝ᵥ βB + xA ⬝ᵥ (βA - βB) := by
  rw [hA, hB, sub_dotProduct, dotProduct_sub]
  ring

/-- **OLS with an intercept fits the means.** If `β` solves the least-squares normal
equations `Xᵀ X β = Xᵀ y` and column `c` of `X` is the intercept (all ones), then the sample
mean outcome equals the average regressor vector times `β`. -/
theorem sampleMean_eq_regressorMean_dotProduct {n : ℕ} {κ : Type*} [Fintype κ]
    {X : Matrix (Fin n) κ ℝ} {y : Fin n → ℝ} {β : κ → ℝ} (c : κ) (hc : ∀ i, X i c = 1)
    (hnormal : Xᵀ *ᵥ (X *ᵥ β) = Xᵀ *ᵥ y) :
    sampleMean y = regressorMean X ⬝ᵥ β := by
  have hproj : ∀ v : Fin n → ℝ, (Xᵀ *ᵥ v) c = ∑ i, v i := by
    intro v
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hc]
  have hcat := congrFun hnormal c
  rw [hproj, hproj] at hcat
  have hexpand : ∑ i, (X *ᵥ β) i = ∑ j, (∑ i, X i j) * β j := by
    simp_rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  simp only [regressorMean, sampleMean_eq_sum_div, dotProduct]
  rw [← hcat, hexpand, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Oaxaca–Blinder decomposition of OLS fits.** For two groups with their own OLS
coefficients (normal equations with a common intercept column `c`), the observed mean outcome
gap equals the explained part `(x̄_A - x̄_B) ⬝ β_B` plus the coefficient part
`x̄_A ⬝ (β_A - β_B)`. -/
theorem sampleMean_sub_eq {nA nB : ℕ} {κ : Type*} [Fintype κ]
    {XA : Matrix (Fin nA) κ ℝ} {XB : Matrix (Fin nB) κ ℝ} {yA : Fin nA → ℝ}
    {yB : Fin nB → ℝ} {βA βB : κ → ℝ} (c : κ) (hcA : ∀ i, XA i c = 1)
    (hcB : ∀ i, XB i c = 1) (hA : XAᵀ *ᵥ (XA *ᵥ βA) = XAᵀ *ᵥ yA)
    (hB : XBᵀ *ᵥ (XB *ᵥ βB) = XBᵀ *ᵥ yB) :
    sampleMean yA - sampleMean yB =
      (regressorMean XA - regressorMean XB) ⬝ᵥ βB + regressorMean XA ⬝ᵥ (βA - βB) := by
  have eA := sampleMean_eq_regressorMean_dotProduct (X := XA) (y := yA) (β := βA) c hcA hA
  have eB := sampleMean_eq_regressorMean_dotProduct (X := XB) (y := yB) (β := βB) c hcB hB
  exact meanGap_eq eA eB

end MathlibExt.Economics.OaxacaBlinder
