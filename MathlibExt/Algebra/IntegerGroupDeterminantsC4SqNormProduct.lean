/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqNormDifference
import Mathlib.Tactic.Ring

/-!
# Gaussian norm products for `C₄ × C₄`

`c4Sq_norm_beta_gamma_eq` expresses the norms of β and γ as products of sums of two squares.
-/

namespace MetaMathlibExt

/-- **Norms of β and γ as products of sums of two squares (C₄²).** Let $a$ be an integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $d_0, \dots, d_7$
and Gaussian integers $\beta$, $\gamma$, and write $\beta\bar\beta$, $\gamma\bar\gamma$ for the
norms of $\beta$ and $\gamma$. Then

$$\beta\bar\beta = \bigl((d_0 + d_2 + d_1 + d_3)^2 + (d_4 + d_6 + d_5 + d_7)^2\bigr)
\bigl((d_0 + d_2 - d_1 - d_3)^2 + (d_4 + d_6 - d_5 - d_7)^2\bigr)$$

and

$$\gamma\bar\gamma = \bigl((d_0 - d_2 - d_5 + d_7)^2 + (d_4 - d_6 + d_1 - d_3)^2\bigr)
\bigl((d_0 - d_2 + d_5 - d_7)^2 + (d_4 - d_6 - d_1 + d_3)^2\bigr).$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 1 (`integers-2024-A30-lem-1`). -/
public theorem c4Sq_norm_beta_gamma_eq (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    Zsqrtd.norm (c4SqBeta a) =
        ((d 0 + d 2 + d 1 + d 3) ^ 2 + (d 4 + d 6 + d 5 + d 7) ^ 2) *
          ((d 0 + d 2 - d 1 - d 3) ^ 2 + (d 4 + d 6 - d 5 - d 7) ^ 2) ∧
      Zsqrtd.norm (c4SqGamma a) =
        ((d 0 - d 2 - d 5 + d 7) ^ 2 + (d 4 - d 6 + d 1 - d 3) ^ 2) *
          ((d 0 - d 2 + d 5 - d 7) ^ 2 + (d 4 - d 6 - d 1 + d 3) ^ 2) := by
  have factor (u v : GaussianInt) :
      u ^ 2 + v ^ 2 = (u + Zsqrtd.sqrtd * v) * (u - Zsqrtd.sqrtd * v) := by
    rw [← sq_sub_sq, mul_pow, show (Zsqrtd.sqrtd : GaussianInt) ^ 2 = -1 by decide]
    ring
  dsimp only
  constructor
  · rw [c4SqBeta, sq_sub_sq, Zsqrtd.norm_mul]
    congr 1 <;> simp [Zsqrtd.norm, c4SqAlpha] <;> ring
  · rw [c4SqGamma, factor, Zsqrtd.norm_mul]
    congr 1 <;> simp [Zsqrtd.norm, c4SqAlpha] <;> ring

end MetaMathlibExt
