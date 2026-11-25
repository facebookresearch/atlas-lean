/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels
public import Mathlib.Tactic.NormNum

/-!
# The genuine SL2 square and its central-quotient boundary

The Weyl lift has square minus identity in SL2. A quotient that kills
this central element has square identity. Requiring nontrivial square
in every reductive target would exclude the PGL2 case.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.CameralNormalizerSquare

open _root_.MathlibExt.AlgebraicGeometry.CameralRootSL2Sources
open _root_.MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels
open _root_.MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels

theorem standardSL2lift_square_ne_one :
    normalizerMatrix (1 : ℂˣ) * normalizerMatrix (1 : ℂˣ) ≠ 1 := by
  rw [normalizerMatrix_square]
  intro h
  have e := congrArg
    (fun m : Matrix.SpecialLinearGroup (Fin 2) ℂ => (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [diagonalMatrix] at e

theorem centralQuotient_square {H : Type} [Group H]
    (q : Matrix.SpecialLinearGroup (Fin 2) ℂ →* H)
    (h : q (diagonalMatrix (-1 : ℂˣ)) = 1) : (q (normalizerMatrix (1 : ℂˣ))) ^ 2 = 1 := by
  rw [pow_two, ← map_mul, normalizerMatrix_square, h]

end MathlibExtTest.AlgebraicGeometry.CameralNormalizerSquare
