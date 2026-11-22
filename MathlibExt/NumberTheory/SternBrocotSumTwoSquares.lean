/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Continued fraction convergents as matrix paths

The alternating product of the right and left moves in the Stern–Brocot tree records two
consecutive convergents in its columns. We use the recurrences from Hongshen Chua,
[Binary Trees and Sum of Two Squares, Theorem 1](https://arxiv.org/html/2606.24931v1#S3).
-/

namespace MetaMathlibExt

/-- The columns of the alternating matrix path are consecutive convergent pairs, with the
latest pair on the right for even indices and on the left for odd indices. The sequences
`A` and `B` start with the initial values for the convergent of index `-1`. -/
public theorem continuedFraction_path_eq_convergents (q A B : ℕ → ℕ)
    (hA₀ : A 0 = 1) (hA₁ : A 1 = q 0) (hA : ∀ k, A (k + 2) = q (k + 1) * A (k + 1) + A k)
    (hB₀ : B 0 = 0) (hB₁ : B 1 = 1) (hB : ∀ k, B (k + 2) = q (k + 1) * B (k + 1) + B k)
    (n : ℕ) :
    ((List.range (n + 1)).map fun i =>
        (if Even i then !![1, 1; 0, 1] else !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^
          q i).prod =
      if Even n then !![A n, A (n + 1); B n, B (n + 1)]
      else !![A (n + 1), A n; B (n + 1), B n] := by
  have rightMove_pow (k : ℕ) :
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^ k = !![1, k; 0, 1] := by
    induction k with
    | zero => exact Matrix.one_fin_two
    | succ k ih => simp [pow_succ, ih, Nat.add_comm]
  have leftMove_pow (k : ℕ) :
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^ k = !![1, 0; k, 1] := by
    induction k with
    | zero => exact Matrix.one_fin_two
    | succ k ih => simp [pow_succ, ih]
  induction n with
  | zero => simp [List.range_succ, hA₀, hA₁, hB₀, hB₁, rightMove_pow]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton,
      List.prod_singleton, hA n, hB n]
    by_cases hn : Even n <;>
      simp [Nat.even_add_one, hn, rightMove_pow, leftMove_pow,
        Nat.mul_comm, Nat.add_comm]

end MetaMathlibExt
