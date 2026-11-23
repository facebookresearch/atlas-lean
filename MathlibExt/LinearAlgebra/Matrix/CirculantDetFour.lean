/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# The four-by-four circulant determinant

Expanding along the first row gives a polynomial identity over any commutative ring.
-/

namespace MetaMathlibExt

@[expose] public section

open Matrix

/-- **The group determinant of $C_4$.** For a commutative ring $R$ and
$x = (x_0, x_1, x_2, x_3) \in R^4$, $D_4(x_0, x_1, x_2, x_3)$ is the determinant of the
$4 \times 4$ circulant matrix whose $(i, j)$ entry is $x_{i - j}$, indices taken mod $4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public def circulantDetFour {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  (circulant x).det

/-- **The 4 × 4 circulant determinant of (1, 0, 0, 0).** Over every commutative ring $R$, the
$4 \times 4$ circulant determinant satisfies $D_4(1, 0, 0, 0) = 1$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public theorem circulantDetFour_single_one {R : Type*} [CommRing R] :
    circulantDetFour (Pi.single 0 1 : Fin 4 → R) = 1 := by
  simp [circulantDetFour]

/-- **Factorization of the 4 × 4 circulant determinant.** For every commutative ring $R$ and all
$x_0, x_1, x_2, x_3 \in R$, the $4 \times 4$ circulant determinant $D_4$ satisfies

$$D_4(x_0, x_1, x_2, x_3) =
\bigl((x_0 + x_2)^2 - (x_1 + x_3)^2\bigr)\bigl((x_0 - x_2)^2 + (x_1 - x_3)^2\bigr).$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 1 (`integers-2024-A30-cor-1`). -/
public theorem circulantDetFour_eq {R : Type*} [CommRing R] (x₀ x₁ x₂ x₃ : R) :
    circulantDetFour ![x₀, x₁, x₂, x₃] =
      ((x₀ + x₂) ^ 2 - (x₁ + x₃) ^ 2) * ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2) := by
  rw [circulantDetFour, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, submatrix_apply, Fin.succAbove]
  ring

end

end MetaMathlibExt
