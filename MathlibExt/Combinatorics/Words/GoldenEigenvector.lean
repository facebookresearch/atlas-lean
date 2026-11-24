/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.Combinatorics.Words.PisaEigenvector

/-!
# Integer matrices with the golden eigenvector

We characterize the integer matrices with right eigenvector `(φ, 1)` and factor their
characteristic polynomials over the reals.
-/

namespace MetaMathlibExt

open Polynomial in
/-- **Integer matrices with the golden eigenvector.** Let $\tau = (1 + \sqrt 5)/2$ be the golden
ratio and $\tau' = (1 - \sqrt 5)/2$ its conjugate, and let $M$ be a $2 \times 2$ integer matrix.
Then $(\tau, 1)^T$ is a right eigenvector of $M$, that is, $M (\tau, 1)^T = c\,(\tau, 1)^T$ for
some real number $c$, if and only if

$$M = \begin{pmatrix} m + n & m \\ m & n \end{pmatrix}$$

for some integers $m$ and $n$. In that case the characteristic polynomial of $M$ is
$(X - (n + m\tau))(X - (n + m\tau'))$, so the eigenvalues of $M$ are $n + m\tau$ and
$n + m\tau'$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 39
(`jis-2025-25.1.5-lem-39`). -/
public theorem golden_eigenvector_iff (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ((∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![Real.goldenRatio, 1] =
        c • ![Real.goldenRatio, 1]) ↔
        ∃ m n : ℤ, M = !![m + n, m; m, n]) ∧
      ∀ m n : ℤ, M = !![m + n, m; m, n] →
        (M.map (Int.cast : ℤ → ℝ)).charpoly =
          (X - C ((n : ℝ) + m * Real.goldenRatio)) * (X - C ((n : ℝ) + m * Real.goldenConj)) := by
  constructor
  · have h := (pisa_eigenvector_iff 1 1 le_rfl le_rfl M).1 (by norm_num)
    simpa only [Nat.cast_one, one_pow, mul_one, one_mul, show (1 : ℝ) + 4 = 5 by norm_num,
      Real.goldenRatio, add_comm] using h
  · rintro m n rfl
    rw [Matrix.charpoly_fin_two]
    apply Polynomial.funext
    intro x
    simp [Matrix.trace_fin_two, Matrix.det_fin_two]
    -- The sum and product of the proposed roots give the trace and determinant.
    linear_combination
      (m : ℝ) * (x - n) * Real.goldenRatio_add_goldenConj -
      (m : ℝ) ^ 2 * Real.goldenRatio_mul_goldenConj

end MetaMathlibExt
