/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursion

/-!
# Type-level tests for the bilinear block encoder and decoder
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    ArithmeticCircuit F
      ((Fin (2 ^ (0 + 1)) × Fin (2 ^ (0 + 1))) ⊕
        (Fin (2 ^ (0 + 1)) × Fin (2 ^ (0 + 1))))
      (Fin terms.length ×
        ((Fin (2 ^ 0) × Fin (2 ^ 0)) ⊕ (Fin (2 ^ 0) × Fin (2 ^ 0)))) :=
  blockEncoder terms 0

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    ArithmeticCircuit F
      ((Fin (2 ^ (1 + 1)) × Fin (2 ^ (1 + 1))) ⊕
        (Fin (2 ^ (1 + 1)) × Fin (2 ^ (1 + 1))))
      (Fin terms.length ×
        ((Fin (2 ^ 1) × Fin (2 ^ 1)) ⊕ (Fin (2 ^ 1) × Fin (2 ^ 1)))) :=
  blockEncoder terms 1

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    ArithmeticCircuit F
      (Fin terms.length × (Fin (2 ^ 0) × Fin (2 ^ 0)))
      (Fin (2 ^ (0 + 1)) × Fin (2 ^ (0 + 1))) :=
  blockDecoder terms 0

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    ArithmeticCircuit F
      (Fin terms.length × (Fin (2 ^ 1) × Fin (2 ^ 1)))
      (Fin (2 ^ (1 + 1)) × Fin (2 ^ (1 + 1))) :=
  blockDecoder terms 1

end Cslib.Complexity.Algebraic
