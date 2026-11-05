/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.ZagierMatrixInverse

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierMatrix K

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierInverseP K

example (K : ℕ) : Matrix (Fin (K - 1)) (Fin (K - 1)) ℚ := MetaMathlibExt.zagierInverseQ K

example := MetaMathlibExt.zagierInverseP_eq_zagierInverseQ 3

example := MetaMathlibExt.zagierMatrix_mul_zagierInverseP 3 (by decide)

example := MetaMathlibExt.zagierInverseP_mul_zagierMatrix 3 (by decide)

example := (MetaMathlibExt.zagier_matrix_inverse 3 (by decide)).2.2
