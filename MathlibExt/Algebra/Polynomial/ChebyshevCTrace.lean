/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Trace formula for the monic Chebyshev polynomials

The matrix with rows `(X, -1)` and `(1, 0)` satisfies `M ^ 2 = X • M - 1`.
Multiplying by `M ^ k` and taking traces gives the Chebyshev recurrence.
-/

open Polynomial

namespace MetaMathlibExt

/-- **Trace formula for the monic Chebyshev polynomials.** Let $\bar T_k \in \mathbb{Z}[X]$ be
the monic Chebyshev polynomials, given by $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$, and let $M$ be the $2 \times 2$ matrix over
$\mathbb{Z}[X]$ with rows $(X, -1)$ and $(1, 0)$. Then $\bar T_k = \operatorname{tr}(M^k)$ for
every natural number $k$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.2
(`jis-2026-26.4.4-prop-7`). -/
public theorem chebyshevC_eq_trace_pow (k : ℕ) :
    Chebyshev.C ℤ k = Matrix.trace ((!![X, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ[X]) ^ k) := by
  let M : Matrix (Fin 2) (Fin 2) ℤ[X] := !![X, -1; 1, 0]
  change Chebyshev.C ℤ k = Matrix.trace (M ^ k)
  have hsq : M ^ 2 = (X : ℤ[X]) • M - 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [M, pow_two, Matrix.one_fin_two, sub_eq_add_neg]
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [M]
  | more k ih₀ ih₁ =>
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.C_add_two, ← Nat.cast_succ, ih₁, ih₀,
      pow_add M k 2, hsq, mul_sub, Matrix.mul_smul, mul_one, ← pow_succ,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

end MetaMathlibExt
