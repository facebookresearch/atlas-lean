/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Abel

/-!
# Aitken's block identity

For real matrices $S_{XX}, V$ of size $p \times p$, $S_{XY}$ of size $p \times q$, and
$S_{YY}$ of size $q \times q$, assume $S_{XX}$ is symmetric and nonsingular. Writing
$B = S_{XY}^{\mathsf T} S_{XX}^{-1}$, `aitken_block_identity` rewrites the two
regression-form covariance blocks $V B^{\mathsf T}$ and
$B V B^{\mathsf T} + (S_{YY} - S_{XY}^{\mathsf T} S_{XX}^{-1} S_{XY})$ as the upper-right and
lower-right blocks of Aitken's equation (7), with $R_{qp} = R_{pq}^{\mathsf T}$.

This is the matrix algebra underlying the block formulas, not a theorem about how selection
changes a distribution. Neither symmetry of $V$ or $S_{YY}$ nor positive definiteness is needed.
Nonsingularity ensures that Mathlib's totalized inverse agrees with the ordinary inverse; the
algebraic rewrites use only symmetry of that inverse.

## References

* A. C. Aitken, *Note on Selection from a Multivariate Normal Population*, Proceedings of the
  Edinburgh Mathematical Society, Series II, 4(2) (1935), 106–110, p. 109, equation (7).
  https://doi.org/10.1017/S0013091500008063. The paper was received and read in 1934.
* Aitken credits the earlier selection formulas to K. Pearson, *Mathematical Contributions to the
  Theory of Evolution. XI.—On the Influence of Natural Selection on the Variability and Correlation
  of Organs*, Philosophical Transactions of the Royal Society of London, Series A, 200 (1903),
  1–66, and the moment-generating-function approach to H. E. Soper, *Frequency Arrays, Illustrating
  the Use of Logical Symbols in the Study of Statistical and Other Distributions*, Cambridge
  University Press (1922), 20–21.
-/

public section

open Matrix

namespace WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted

variable {p q : ℕ}

/-- **Aitken's block identity** (Aitken 1934, (7)). Let `Σ_XX` be a symmetric `p × p` real
matrix with nonzero determinant, let `Σ_XY` be a `p × q` and `Σ_YY` a `q × q` real matrix, and
let `V` be any `p × p` real matrix (the selected covariance of `X`). Put `B = Σ_XYᵀ Σ_XX⁻¹`.
Then `V Bᵀ = V Σ_XX⁻¹ Σ_XY`, and
`B V Bᵀ + (Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY) = Σ_YY - Σ_XYᵀ (Σ_XX⁻¹ - Σ_XX⁻¹ V Σ_XX⁻¹) Σ_XY`.
So the regression-form selected covariance blocks, with the population regression coefficient `B`
and residual covariance `Σ_YY - Σ_XYᵀ Σ_XX⁻¹ Σ_XY`, are Aitken's blocks.

Source: Aitken (1934), p. 109, equation (7). -/
theorem aitken_block_identity (Sxx : Matrix (Fin p) (Fin p) ℝ)
    (Sxy : Matrix (Fin p) (Fin q) ℝ) (Syy : Matrix (Fin q) (Fin q) ℝ)
    (V : Matrix (Fin p) (Fin p) ℝ) (hsym : Sxx.IsSymm) (_hdet : IsUnit Sxx.det) :
    V * (Sxyᵀ * Sxx⁻¹)ᵀ = V * Sxx⁻¹ * Sxy ∧
      Sxyᵀ * Sxx⁻¹ * V * (Sxyᵀ * Sxx⁻¹)ᵀ + (Syy - Sxyᵀ * Sxx⁻¹ * Sxy) =
        Syy - Sxyᵀ * (Sxx⁻¹ - Sxx⁻¹ * V * Sxx⁻¹) * Sxy := by
  rw [transpose_mul, hsym.inv.eq, transpose_transpose]
  constructor
  · exact (Matrix.mul_assoc V Sxx⁻¹ Sxy).symm
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel

end WantedExt.Biology.StatisticalGenetics.PearsonAitkenLawleySelectionWanted
