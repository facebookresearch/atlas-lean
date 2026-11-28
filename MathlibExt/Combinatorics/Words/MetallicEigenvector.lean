/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.IsSquare
import MathlibExt.Combinatorics.Words.PisaEigenvector

/-!
# Integer matrices with a metallic-mean eigenvector

The metallic mean is the Pisa root with parameter `m = 1`; its discriminant is never a square
for `k ≥ 1`. The sum and product of the two metallic roots give the characteristic polynomial.
-/

namespace MetaMathlibExt

private theorem metallic_eigenvector_iff.discriminant_not_isSquare (k : ℕ) (hk : 1 ≤ k) :
    ¬ IsSquare (k ^ 2 + 4) := by
  by_cases h : k = 1
  · subst k
    norm_num
  · have hk₂ : 2 ≤ k := by omega
    have hlt : k ^ 2 + 4 < (k + 1) ^ 2 := calc
      k ^ 2 + 4 < k ^ 2 + (2 * k + 1) := by omega
      _ = (k + 1) ^ 2 := by ring
    rintro ⟨r, hr⟩
    exact Nat.not_exists_sq' (by omega) hlt ⟨r, by simpa only [pow_two] using hr.symm⟩

open Polynomial in
/-- **Integer matrices with a metallic-mean eigenvector.** Let $k \ge 1$ be an integer, let
$\tau_k = (k + \sqrt{k^2 + 4})/2$ and $\tau_k' = (k - \sqrt{k^2 + 4})/2$, and let $M$ be a
$2 \times 2$ integer matrix. Then $(\tau_k, 1)^T$ is a right eigenvector of $M$ over $\mathbb{R}$
if and only if $M$ has rows $(km + n, m)$ and $(m, n)$ for some integers $m, n$. For such $M$ the
characteristic polynomial of $M$ is $(X - (n + m\tau_k))(X - (n + m\tau_k'))$, so the eigenvalues
of $M$ are $n + m\tau_k$ and $n + m\tau_k'$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 66
(`jis-2025-25.1.5-lem-66`). -/
public theorem metallic_eigenvector_iff (k : ℕ) (hk : 1 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    let τ : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2
    let τ' : ℝ := (k - Real.sqrt (k ^ 2 + 4)) / 2
    ((∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]) ↔
        ∃ m n : ℤ, M = !![k * m + n, m; m, n]) ∧
      ∀ m n : ℤ, M = !![k * m + n, m; m, n] →
        (M.map (Int.cast : ℤ → ℝ)).charpoly =
          (X - C ((n : ℝ) + m * τ)) * (X - C ((n : ℝ) + m * τ')) := by
  intro τ τ'
  constructor
  · -- The nonsquare case of the Pisa lemma eliminates the eigenvalue and compares coefficients.
    have h := (pisa_eigenvector_iff k 1 hk le_rfl M).1
      (metallic_eigenvector_iff.discriminant_not_isSquare k hk)
    simpa only [Nat.cast_one, mul_one, one_mul, mul_comm, add_comm] using h
  · have hsum : τ + τ' = (k : ℝ) := by
      dsimp only [τ, τ']
      ring
    have hprod : τ * τ' = -1 := by
      dsimp only [τ, τ']
      linear_combination -Real.sq_sqrt (show 0 ≤ (k : ℝ) ^ 2 + 4 by positivity) / 4
    clear_value τ τ'
    intro m n hM
    -- Vieta's identities identify the trace and determinant with the sum and product of the roots.
    have htrace : (M.map (Int.cast : ℤ → ℝ)).trace =
        ((n : ℝ) + m * τ) + ((n : ℝ) + m * τ') := by
      simp [hM, Matrix.trace_fin_two]
      linear_combination -(m : ℝ) * hsum
    have hdet : (M.map (Int.cast : ℤ → ℝ)).det =
        ((n : ℝ) + m * τ) * ((n : ℝ) + m * τ') := by
      simp [hM, Matrix.det_fin_two]
      linear_combination -(m : ℝ) * n * hsum - (m : ℝ) ^ 2 * hprod
    rw [Matrix.charpoly_fin_two, htrace, hdet, C_add, C_mul]
    ring

end MetaMathlibExt
