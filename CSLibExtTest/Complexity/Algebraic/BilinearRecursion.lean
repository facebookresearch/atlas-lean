/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursion

/-!
# Type-level tests for the recursive bilinear circuit
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

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    MatrixArithmeticCircuit F 1 1 1 :=
  recursiveCircuit terms 0

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    MatrixArithmeticCircuit F 2 2 2 :=
  recursiveCircuit terms 1

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2))) :
    MatrixArithmeticCircuit F 4 4 4 :=
  recursiveCircuit terms 2

noncomputable example {F : Type u} [Field F] :
    ∃ terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)),
      terms.length ≤ 7 ∧ IsMatrixMultiplication (recursiveCircuit terms 1) :=
  exists_recursiveCircuit_isMatrixMultiplication
    (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor_rank_le_seven F) 1

noncomputable example {F : Type u} [Field F] :
    ∃ terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)),
      terms.length ≤ 7 ∧ IsMatrixMultiplication (recursiveCircuit terms 2) :=
  exists_recursiveCircuit_isMatrixMultiplication
    (MatrixMultiplicationExponent.squareMatrixMultiplicationTensor_rank_le_seven F) 2

noncomputable example {F : Type u} [Field F]
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)
      (MatrixMultiplicationExponent.MatrixCoordinate 2 2)))
    (hterms : ∀ a b c,
      MatrixMultiplicationExponent.squareMatrixMultiplicationTensor F 2 a b c =
        (terms.map fun term ↦ term.eval a b c).sum) :
    IsMatrixMultiplication (recursiveCircuit terms 0) :=
  recursiveCircuit_isMatrixMultiplication terms hterms 0

end Cslib.Complexity.Algebraic
