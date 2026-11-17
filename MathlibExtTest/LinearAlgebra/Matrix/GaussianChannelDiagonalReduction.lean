/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction

/-- Channel eigenvalues are nonnegative for the identity noise
covariance. -/
example (H : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    0 ≤ channelEigenvalues H Matrix.PosDef.one i :=
  channelEigenvalues_nonneg H Matrix.PosDef.one i

end MathlibExtTest.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction
