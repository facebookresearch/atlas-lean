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
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel

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

The block form below replaces the single regressor `z` by a matrix `Z`, its scalar coefficient
by a vector `g`, and `z⊥` by `Z⊥ = Z - A U`, where `U` solves the weighted normal equations
`Aᵀ W Z⊥ = 0`. It proves `(Z⊥ᵀ W Z⊥) g = Z⊥ᵀ W y`, the same identity with `y` replaced by
`y - A v`, and the solved form when the residualized Gram matrix is nonsingular. As in the scalar
case, the identities need no positivity or rank hypothesis; nonsingularity is used only to solve
for `g`.

Stratified LD-score regression with covariates (LDSC-SEG, Finucane et al. 2018) and signed LD
profile regression with a signed background model (Reshef et al. 2018) both report the coefficient
of one regressor after conditioning on others; this file gives the exact algebra behind that step.

## Main results

* `Matrix.frischWaughLovell`: `t ⟪z⊥, z⊥⟫_W = ⟪z⊥, y⟫_W`.
* `Matrix.frischWaughLovell_residual`: the same with the residualized response.
* `Matrix.frischWaughLovell_eq_div`: `t = ⟪z⊥, y⊥⟫_W / ⟪z⊥, z⊥⟫_W` when the denominator is
  nonzero.
* `Matrix.frischWaughLovell_block`: `(Z⊥ᵀ W Z⊥) g = Z⊥ᵀ W y` for a regressor block.
* `Matrix.frischWaughLovell_block_residual`: the block identity with `y - A v` in place of `y`.
* `Matrix.frischWaughLovell_block_eq_inv`: the solved block coefficient when
  `Z⊥ᵀ W Z⊥` is nonsingular.

## References

* R. Frisch, F. V. Waugh, *Partial time regressions as compared with individual trends*,
  Econometrica 1 (1933), 387–401.
* M. C. Lovell, *Seasonal adjustment of economic time series and multiple regression analysis*,
  J. Amer. Statist. Assoc. 58 (1963), 993–1010.
-/

@[expose] public section

namespace Matrix

variable {m κ π : Type*} [Fintype m] [Fintype κ] [Fintype π]

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

/-- **Frisch–Waugh–Lovell, block form** for weighted least squares with a symmetric weight
matrix `W`: if `(b, g)` solves the normal equations of the regression of `y` on `[A | Z]` and
`Z⊥ = Z - A U` is the weighted residual of the block `Z` on `A` (`Aᵀ W Z⊥ = 0`), then the
coefficient block satisfies `(Z⊥ᵀ W Z⊥) g = Z⊥ᵀ W y`. -/
theorem frischWaughLovell_block
    {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m κ ℝ} {Z : Matrix m π ℝ}
    {y : m → ℝ} {b : κ → ℝ} {U : Matrix κ π ℝ} {g : π → ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hZ : Zᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hU : Aᵀ * (W * (Z - A * U)) = 0) :
    ((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g =
      (Z - A * U)ᵀ *ᵥ (W *ᵥ y) := by
  have hZp : ((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g
      = (Z - A * U)ᵀ *ᵥ (W *ᵥ ((Z - A * U) *ᵥ g)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have horthA : ∀ v : κ → ℝ, (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v)) = 0 := by
    intro v
    have h1 : (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v))
        = ((Z - A * U)ᵀ * W * A) *ᵥ v := by
      calc (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v))
          = ((Z - A * U)ᵀ * W) *ᵥ (A *ᵥ v) := Matrix.mulVec_mulVec _ _ _
        _ = ((Z - A * U)ᵀ * W * A) *ᵥ v := Matrix.mulVec_mulVec _ _ _
    have h2 : (Z - A * U)ᵀ * W * A = 0 := by
      have hmat : (Z - A * U)ᵀ * W * A = (Aᵀ * (W * (Z - A * U)))ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW]
      rw [hmat, hU, Matrix.transpose_zero]
    rw [h1, h2, Matrix.zero_mulVec]
  have horthE : (Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0 := by
    have hexpand : (Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g))
        = Zᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g))
          - Uᵀ *ᵥ (Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g))) := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.sub_mulVec,
        ← Matrix.mulVec_mulVec]
    rw [hexpand, hZ, hA, Matrix.mulVec_zero, sub_zero]
  have hdecomp : (Z - A * U)ᵀ *ᵥ (W *ᵥ y)
      = (Z - A * U)ᵀ *ᵥ (W *ᵥ ((Z - A * U) *ᵥ g)) := by
    have hsplit : y
        = (y - A *ᵥ b - Z *ᵥ g) + A *ᵥ b + A *ᵥ (U *ᵥ g)
          + (Z - A * U) *ᵥ g := by
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      abel
    rw [hsplit]
    simp only [Matrix.mulVec_add, horthE, horthA, zero_add, add_zero]
  rw [hZp]
  exact hdecomp.symm

/-- **Frisch–Waugh–Lovell, block residualized form**: under the hypotheses of
`frischWaughLovell_block`, replacing `y` by `y - A v` for any `v` does not change the right-hand
side. In particular, this applies when `y - A v` is the weighted residual of `y` on `A`. -/
theorem frischWaughLovell_block_residual
    {W : Matrix m m ℝ} (hW : Wᵀ = W) {A : Matrix m κ ℝ}
    {Z : Matrix m π ℝ} {y : m → ℝ} {b v : κ → ℝ} {U : Matrix κ π ℝ}
    {g : π → ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hZ : Zᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hU : Aᵀ * (W * (Z - A * U)) = 0) :
    ((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g =
      (Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ v)) := by
  have hmain : ((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g
      = (Z - A * U)ᵀ *ᵥ (W *ᵥ y) :=
    frischWaughLovell_block hW hA hZ hU
  have horth : (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v)) = 0 := by
    have h1 : (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v))
        = ((Z - A * U)ᵀ * W * A) *ᵥ v := by
      calc (Z - A * U)ᵀ *ᵥ (W *ᵥ (A *ᵥ v))
          = ((Z - A * U)ᵀ * W) *ᵥ (A *ᵥ v) := Matrix.mulVec_mulVec _ _ _
        _ = ((Z - A * U)ᵀ * W * A) *ᵥ v := Matrix.mulVec_mulVec _ _ _
    have h2 : (Z - A * U)ᵀ * W * A = 0 := by
      have hmat : (Z - A * U)ᵀ * W * A = (Aᵀ * (W * (Z - A * U)))ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hW]
      rw [hmat, hU, Matrix.transpose_zero]
    rw [h1, h2, Matrix.zero_mulVec]
  have hsub : (Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ v))
      = (Z - A * U)ᵀ *ᵥ (W *ᵥ y) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, horth, sub_zero]
  rw [hmain]
  exact hsub.symm

/-- **Frisch–Waugh–Lovell, block solved form**: under the hypotheses of
`frischWaughLovell_block_residual`, if the residualized Gram matrix `Z⊥ᵀ W Z⊥` is nonsingular,
then `g = (Z⊥ᵀ W Z⊥)⁻¹ Z⊥ᵀ W (y - A v)`. -/
theorem frischWaughLovell_block_eq_inv [DecidableEq π]
    {W : Matrix m m ℝ} (hW : Wᵀ = W)
    {A : Matrix m κ ℝ} {Z : Matrix m π ℝ} {y : m → ℝ} {b v : κ → ℝ}
    {U : Matrix κ π ℝ} {g : π → ℝ}
    (hA : Aᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hZ : Zᵀ *ᵥ (W *ᵥ (y - A *ᵥ b - Z *ᵥ g)) = 0)
    (hU : Aᵀ * (W * (Z - A * U)) = 0)
    (hG : IsUnit ((Z - A * U)ᵀ * W * (Z - A * U)).det) :
    g = ((Z - A * U)ᵀ * W * (Z - A * U))⁻¹ *ᵥ
      ((Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ v))) := by
  have hmain : ((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g
      = (Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ v)) :=
    frischWaughLovell_block_residual hW hA hZ hU
  have hMinv : ((Z - A * U)ᵀ * W * (Z - A * U))⁻¹
      * ((Z - A * U)ᵀ * W * (Z - A * U)) = 1 :=
    Matrix.nonsing_inv_mul _ hG
  calc g = ((Z - A * U)ᵀ * W * (Z - A * U))⁻¹ *ᵥ
        (((Z - A * U)ᵀ * W * (Z - A * U)) *ᵥ g) := by
        rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
    _ = ((Z - A * U)ᵀ * W * (Z - A * U))⁻¹ *ᵥ
        ((Z - A * U)ᵀ *ᵥ (W *ᵥ (y - A *ᵥ v))) := by
        rw [hmain]

end Matrix
