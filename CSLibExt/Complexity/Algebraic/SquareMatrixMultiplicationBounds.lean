/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
import CSLibExt.Complexity.Algebraic.DualMatrixMultiplicationBoundsRectangularOperationRankBridge

/-!
# The square operation/rank bridge

Over every infinite field, `squareOperationRankBridge` identifies the square circuit exponent
`squareMatrixMultiplicationCircuitExponent` with the tensor-rank exponent
`MatrixMultiplicationExponent.matrixMultiplicationExponent`, the equivalence surveyed in
[B2013] (Bläser, *Fast matrix multiplication*, 2013).

The square circuit exponent is the rectangular circuit exponent at aspect `1`, so the
rectangular bridge `rectangularOperationRankBridge` at aspect `1` equates it with the
rectangular rank exponent at aspect `1`. That rank exponent admits `w` when every `w + ε` with
`ε > 0` bounds the rank, while the square rank exponent takes the infimum of direct `O(n ^ w)`
rank bounds; a private comparison shows that the two infima agree.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic MatrixMultiplicationExponent

universe u

/-- The rectangular rank exponent at aspect `1` equals the square rank exponent. -/
private theorem rectangularMatrixMultiplicationExponent_one (F : Type u) [Field F] :
    rectangularMatrixMultiplicationExponent F 1 = matrixMultiplicationExponent F := by
  apply le_antisymm
  · apply le_matrixMultiplicationExponent
    intro w hw
    refine sInf_le ⟨w, rfl, zero_le_one, hw.1, fun ε hε => ?_⟩
    obtain ⟨-, C, hC, N, hN, hbound⟩ := hw.mono F (le_add_of_nonneg_right hε.le)
    refine ⟨C, hC, N, hN, fun n hn => ?_⟩
    rw [rectangularInnerDimension_one]
    exact hbound n hn
  · apply le_sInf
    rintro _ ⟨w, rfl, -, hw, hbound⟩
    refine (matrixMultiplicationExponent_le_iff F w hw).mpr fun ε hε => ?_
    obtain ⟨C, hC, N, hN, hrank⟩ := hbound ε hε
    refine ⟨add_nonneg hw hε.le, C, hC, N, hN, fun n hn => ?_⟩
    have h := hrank n hn
    rw [rectangularInnerDimension_one] at h
    exact h

/-- **Circuit size and tensor rank give the same square exponent.** For every infinite field $F$,
the square matrix multiplication exponent of $F$ defined by arithmetic-circuit size equals the
matrix multiplication exponent of $F$ defined by tensor rank.

Source: C15a additional comments and [B2013]: the arithmetic-operation
exponent agrees with the tensor-rank exponent. -/
theorem squareOperationRankBridge :
    ∀ (F : Type u) [Field F] [Infinite F],
      squareMatrixMultiplicationCircuitExponent F =
        MatrixMultiplicationExponent.matrixMultiplicationExponent F := by
  intro F _ _
  rw [squareMatrixMultiplicationCircuitExponent_def,
    DualMatrixMultiplicationBoundsWanted.rectangularOperationRankBridge F 1 zero_le_one,
    rectangularMatrixMultiplicationExponent_one]

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
