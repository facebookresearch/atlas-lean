/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.Matrix.TraceNorm

/-!
# Full and half-normalized canonical trace distances

For arbitrary finite square complex matrices `M,N`, define
`traceNormDist(M,N) = Matrix.traceNorm(M-N)` and
`traceDist(M,N) = (1/2) * Matrix.traceNorm(M-N)`, where the canonical trace norm is
`Re (Tr (sqrt ((M-N)ᴴ * (M-N))))`. These distances are nonnegative and symmetric,
and vanish exactly when `M = N`. The full distance is twice the half-normalized distance.
Zero matrices and empty index types are included; positivity and trace-one assumptions
on the inputs are not required.
-/

@[expose] public section

open Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- Full trace-norm distance between square complex matrices: `‖M - N‖₁`.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included. -/
noncomputable def traceNormDist (M N : Matrix n n ℂ) : ℝ :=
  (M - N).traceNorm

/-- The full trace distance is the trace norm of the matrix difference.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_def (M N : Matrix n n ℂ) :
    traceNormDist M N = (M - N).traceNorm
``` -/
theorem traceNormDist_def (M N : Matrix n n ℂ) :
    traceNormDist M N = (M - N).traceNorm := rfl

/-- Standard quantum trace distance `(1/2)‖M - N‖₁`.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included. -/
noncomputable def traceDist (M N : Matrix n n ℂ) : ℝ :=
  (1 / 2 : ℝ) * traceNormDist M N

/-- The half-normalized trace distance is one-half the trace norm of the matrix difference.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_def (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * (M - N).traceNorm
``` -/
theorem traceDist_def (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * (M - N).traceNorm := rfl

/-- The half-normalized trace distance is exactly one-half the full trace distance.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_eq_half_traceNormDist (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * traceNormDist M N
``` -/
theorem traceDist_eq_half_traceNormDist (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * traceNormDist M N := rfl

/-- The full trace distance is exactly twice the half-normalized trace distance.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_eq_two_mul_traceDist (M N : Matrix n n ℂ) :
    traceNormDist M N = 2 * traceDist M N
``` -/
theorem traceNormDist_eq_two_mul_traceDist (M N : Matrix n n ℂ) :
    traceNormDist M N = 2 * traceDist M N := by
  unfold traceDist traceNormDist
  ring

/-- Full trace distance between finite complex matrices is nonnegative.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceNormDist M N
``` -/
theorem traceNormDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceNormDist M N :=
  Matrix.traceNorm_nonneg _

/-- Half-normalized trace distance between finite complex matrices is nonnegative.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceDist M N
``` -/
theorem traceDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceDist M N := by
  unfold traceDist
  apply mul_nonneg
  · norm_num
  · exact traceNormDist_nonneg _ _

/-- The full trace distance from a matrix to itself is zero.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_self (M : Matrix n n ℂ) :
    traceNormDist M M = 0
``` -/
@[simp]
theorem traceNormDist_self (M : Matrix n n ℂ) :
    traceNormDist M M = 0 := by
  simp [traceNormDist]

/-- The half-normalized trace distance from a matrix to itself is zero.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_self (M : Matrix n n ℂ) :
    traceDist M M = 0
``` -/
@[simp]
theorem traceDist_self (M : Matrix n n ℂ) :
    traceDist M M = 0 := by
  simp [traceDist]

/-- Full trace distance is symmetric in the two matrices.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_comm (M N : Matrix n n ℂ) :
    traceNormDist M N = traceNormDist N M
``` -/
theorem traceNormDist_comm (M N : Matrix n n ℂ) :
    traceNormDist M N = traceNormDist N M := by
  unfold traceNormDist
  have h : M - N = -(N - M) := by ext i j; simp
  rw [h, Matrix.traceNorm_neg]

/-- Half-normalized trace distance is symmetric in the two matrices.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_comm (M N : Matrix n n ℂ) :
    traceDist M N = traceDist N M
``` -/
theorem traceDist_comm (M N : Matrix n n ℂ) :
    traceDist M N = traceDist N M := by
  unfold traceDist
  rw [traceNormDist_comm]

/-- Full trace distance is zero exactly when the matrices are equal.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_eq_zero_iff (M N : Matrix n n ℂ) :
    traceNormDist M N = 0 ↔ M = N
``` -/
theorem traceNormDist_eq_zero_iff (M N : Matrix n n ℂ) :
    traceNormDist M N = 0 ↔ M = N := by
  rw [traceNormDist_def, Matrix.traceNorm_zero_iff, sub_eq_zero]

/-- Half-normalized trace distance is zero exactly when the matrices are equal.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_eq_zero_iff (M N : Matrix n n ℂ) :
    traceDist M N = 0 ↔ M = N
``` -/
theorem traceDist_eq_zero_iff (M N : Matrix n n ℂ) :
    traceDist M N = 0 ↔ M = N := by
  constructor
  · intro h
    unfold traceDist at h
    have h_half_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have h0 : traceNormDist M N = 0 := by
      have : (1 / 2 : ℝ) * traceNormDist M N = 0 := h
      exact (mul_eq_zero.mp this).resolve_left h_half_ne
    exact (traceNormDist_eq_zero_iff _ _).mp h0
  · rintro rfl
    exact traceDist_self _

end Matrix
