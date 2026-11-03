/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The Frisch–Waugh–Lovell theorem for weighted least squares

Regress a response `y` on a design `[A | z]` by weighted (generalized) least squares with a
symmetric weight matrix `W`, and let `(b, t)` satisfy the normal equations

  `Aᵀ W (y - A b - t z) = 0`,  `zᵀ W (y - A b - t z) = 0`.

Let `z⊥ = z - A u` be the residual of `z` after weighted regression on `A`
(`Aᵀ W z⊥ = 0`). Then the coefficient `t` of `z` satisfies

  `t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⟫_W`,

and the same holds with `y` replaced by its own residual `y⊥ = y - A v` (`Aᵀ W y⊥ = 0`):
partialling the covariates `A` out of both the response and the regressor of interest leaves the
coefficient unchanged (Frisch and Waugh 1933; Lovell 1963). No positivity of `W`, no full rank
and no uniqueness of the solutions is needed for the identity; when `⟪z⊥, z⊥⟫_W ≠ 0` it
determines `t`.

Stratified LD-score regression with covariates (LDSC-SEG, Finucane et al. 2018) and signed LD
profile regression with a signed background model (Reshef et al. 2018) both report the coefficient
of one regressor after conditioning on others; this file gives the exact algebra behind that step.

## Main results

* `Matrix.frischWaughLovell`: `t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⟫_W`.
* `Matrix.frischWaughLovell_residual`: the same with the residualized response.
* `Matrix.frischWaughLovell_eq_div`: `t = ⟪z⊥, y⊥⟫_W / ⟪z⊥, z⊥⟫_W` when the denominator is
  nonzero.

## References

* R. Frisch, F. V. Waugh, *Partial time regressions as compared with individual trends*,
  Econometrica 1 (1933), 387–401.
* M. C. Lovell, *Seasonal adjustment of economic time series and multiple regression analysis*,
  J. Amer. Statist. Assoc. 58 (1963), 993–1010.
-/

@[expose] public section

namespace Matrix

variable {m κ : Type*} [Fintype m] [Fintype κ]

private theorem dotProduct_mulVec_symm {W : Matrix m m ℝ} (hW : Wᵀ = W) (x y : m → ℝ) :
    x ⬝ᵥ (W *ᵥ y) = y ⬝ᵥ (W *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]

private theorem mulVec_dotProduct_eq (A : Matrix m κ ℝ) (v : κ → ℝ) (w : m → ℝ) :
    (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- **Frisch–Waugh–Lovell** for weighted least squares with a symmetric weight matrix `W`: if
`(b, t)` solves the normal equations of the regression of `y` on `[A | z]` and `z⊥ = z - A u`
is the weighted residual of `z` on `A` (`Aᵀ W z⊥ = 0`), then `t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⟫_W`, where
`⟪x, y⟫_W = x ⬝ᵥ W y`. -/
theorem frischWaughLovell {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m κ ℝ}
    {y z : m → ℝ} {b u : κ → ℝ} {t : ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hz : z ⬝ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hu : Aᵀ *ᵥ (W *ᵥ (z - A *ᵥ u)) = 0) :
    t * ((z - A *ᵥ u) ⬝ᵥ (W *ᵥ (z - A *ᵥ u))) = (z - A *ᵥ u) ⬝ᵥ (W *ᵥ y) := by
  set e := y - A *ᵥ b - t • z with he
  set zp := z - A *ᵥ u with hzp
  have h1 : zp ⬝ᵥ (W *ᵥ e) = 0 := by
    rw [hzp, sub_dotProduct, hz, mulVec_dotProduct_eq, hA, dotProduct_zero, sub_zero]
  have h2 (v : κ → ℝ) : zp ⬝ᵥ (W *ᵥ (A *ᵥ v)) = 0 := by
    rw [dotProduct_mulVec_symm hW, mulVec_dotProduct_eq, hu, dotProduct_zero]
  have hy : y = e + A *ᵥ b + t • (zp + A *ᵥ u) := by
    rw [he, hzp]
    module
  rw [hy, mulVec_add, mulVec_add, mulVec_smul, mulVec_add, dotProduct_add, dotProduct_add,
    dotProduct_smul, dotProduct_add, h1, h2, h2, smul_eq_mul]
  ring

/-- **Frisch–Waugh–Lovell, residualized form**: under the hypotheses of `frischWaughLovell`, if
also `y⊥ = y - A v` is the weighted residual of `y` on `A` (`Aᵀ W y⊥ = 0`), then
`t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⊥⟫_W`: the coefficient of `z` in the full regression is the coefficient of
the regression of the residualized response on the residualized regressor. -/
theorem frischWaughLovell_residual {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m κ ℝ}
    {y z : m → ℝ} {b u v : κ → ℝ} {t : ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hz : z ⬝ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hu : Aᵀ *ᵥ (W *ᵥ (z - A *ᵥ u)) = 0) :
    t * ((z - A *ᵥ u) ⬝ᵥ (W *ᵥ (z - A *ᵥ u))) = (z - A *ᵥ u) ⬝ᵥ (W *ᵥ (y - A *ᵥ v)) := by
  rw [frischWaughLovell hW hA hz hu, mulVec_sub, dotProduct_sub,
    dotProduct_mulVec_symm hW _ (A *ᵥ v), mulVec_dotProduct_eq, hu, dotProduct_zero, sub_zero]

/-- **Frisch–Waugh–Lovell, solved form**: under the hypotheses of `frischWaughLovell_residual`, if
`⟪z⊥, z⊥⟫_W ≠ 0` then `t = ⟪z⊥, y⊥⟫_W / ⟪z⊥, z⊥⟫_W`. -/
theorem frischWaughLovell_eq_div {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m κ ℝ}
    {y z : m → ℝ} {b u v : κ → ℝ} {t : ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hz : z ⬝ᵥ (W *ᵥ (y - A *ᵥ b - t • z)) = 0)
    (hu : Aᵀ *ᵥ (W *ᵥ (z - A *ᵥ u)) = 0)
    (hne : (z - A *ᵥ u) ⬝ᵥ (W *ᵥ (z - A *ᵥ u)) ≠ 0) :
    t = (z - A *ᵥ u) ⬝ᵥ (W *ᵥ (y - A *ᵥ v)) / ((z - A *ᵥ u) ⬝ᵥ (W *ᵥ (z - A *ᵥ u))) := by
  rw [eq_div_iff hne, frischWaughLovell_residual (v := v) hW hA hz hu]

end Matrix
