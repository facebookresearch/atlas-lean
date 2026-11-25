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

public import MathlibExt.LinearAlgebra.Matrix.StableModule

/-! The actual natural-number semimodule case needs neither a ring nor additive negatives. -/

@[expose] public section

example (B : Matrix (Fin 1) (Fin 1) ℕ) :
    Matrix.StableModule.finsuppEquiv ℕ ℕ (Matrix.StableModule.ofFinite ℕ ℕ 1 B) (0, 0) =
      B 0 0 :=
  Matrix.StableModule.entries_ofFinite_fin ℕ ℕ 1 B 0 0

example (B : Matrix (Fin 1) (Fin 1) ℕ) :
    Matrix.zeroExtendLinear (k := ℕ) (A := ℕ) (show 1 ≤ 2 by decide) B 0 0 = B 0 0 :=
  Matrix.zeroExtend_castLE (show 1 ≤ 2 by decide) B 0 0
