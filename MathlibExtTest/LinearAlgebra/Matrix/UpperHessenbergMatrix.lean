/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.UpperHessenbergMatrix

namespace Matrix

example (n : ℕ) : IsUpperHessenberg (1 : Matrix (Fin n) (Fin n) ℤ) := by
  rw [isUpperHessenberg_fin_iff]
  intro i j hij
  simp only [one_apply]
  split_ifs
  · omega
  · rfl

end Matrix
