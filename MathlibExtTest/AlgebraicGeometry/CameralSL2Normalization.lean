/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRootSL2Sources
public import Mathlib.Tactic.NormNum

/-!
# Rank-one conjugation and the nonprimitive-coroot lift regression

Conjugation by diag(a,1) sends the actual SL2 normalizer n(c) to n(ac)
over every commutative coefficient ring. In particular a=-1 changes the
reference lift to its negative. Ramification beta must retain that lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.CameralSL2Normalization

open MathlibExt.AlgebraicGeometry.CameralRootSL2Sources
open MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels
open scoped Matrix

theorem normalizer_conjugation {R : Type} [CommRing R] (a c : Rˣ) :
    conjugatingMatrix a * (normalizerMatrix c).toGL * (conjugatingMatrix a)⁻¹ =
      (normalizerMatrix (a * c)).toGL := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatingMatrix, normalizerMatrix, diagonalMatrix, weylMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm]

theorem minus_one_changes_reference_lift :
    (conjugatingMatrix (-1 : ℂˣ) * (normalizerMatrix (1 : ℂˣ)).toGL *
      (conjugatingMatrix (-1 : ℂˣ))⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) = -weylMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugatingMatrix, normalizerMatrix, diagonalMatrix, weylMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem reference_lift_sign_is_not_erased :
    (normalizerMatrix (-1 : ℂˣ) : Matrix (Fin 2) (Fin 2) ℂ) ≠ normalizerMatrix (1 : ℂˣ) := by
  intro h
  have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 1) h
  norm_num [normalizerMatrix, diagonalMatrix, weylMatrix, Matrix.mul_apply, Fin.sum_univ_two] at he

end MathlibExtTest.AlgebraicGeometry.CameralSL2Normalization
