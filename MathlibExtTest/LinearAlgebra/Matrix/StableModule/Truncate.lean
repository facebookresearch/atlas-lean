/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.StableModule.Truncate

/-! Actual finite-stage retraction with natural-number semimodule coefficients. -/

@[expose] public section

example (r : ℕ) (X : Matrix (Fin r) (Fin r) ℕ) :
    Matrix.StableModule.truncate ℕ ℕ r (Matrix.StableModule.ofFinite ℕ ℕ r X) = X :=
  Matrix.StableModule.truncate_ofFinite ℕ ℕ r X

example (X : Matrix.StableModule ℕ ℕ) : Matrix.StableModule.truncate ℕ ℕ 0 X = 0 := by
  ext i
  exact Fin.elim0 i
