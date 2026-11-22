/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrices with positive minors

`Matrix.HasPositiveMinors`: every finite square submatrix selected by strictly increasing row
and column maps has positive determinant (total positivity). The strict counterpart of
`Matrix.HasNonnegativeMinors`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A rectangular real matrix has positive minors (is totally positive) when every finite square
submatrix selected by strictly increasing row and column maps has positive determinant. The
quantification over all `k : ℕ` includes the `0 × 0` minor, whose determinant is `1`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz
Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026),
Article 26.2.5, Section 1 (total positivity). -/
public def Matrix.HasPositiveMinors {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
    (M : Matrix ι κ ℝ) : Prop :=
  ∀ (k : ℕ) (r : Fin k → ι) (c : Fin k → κ),
    StrictMono r → StrictMono c → 0 < (M.submatrix r c).det

/-- Every entry of a matrix with positive minors is positive (its `1 × 1` minors).

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz
Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026),
Article 26.2.5, Section 1 (total positivity). -/
public theorem Matrix.HasPositiveMinors.entry_pos {ι κ : Type*} [LinearOrder ι]
    [LinearOrder κ] {M : Matrix ι κ ℝ} (hM : Matrix.HasPositiveMinors M) (i : ι) (j : κ) :
    0 < M i j := by
  have h := hM 1 (fun _ => i) (fun _ => j) (fun a b hab => by omega) (fun a b hab => by omega)
  rwa [Matrix.det_unique] at h

end

end MetaMathlibExt
