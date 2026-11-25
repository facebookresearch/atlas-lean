/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotients
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Source word and rank-one lift regressions

The non-involutive pair distinguishes the source commutator order:
A^-1 B^-1 A B has upper-right entry1/2. A genus-two tuple satisfying
the actual -I relation is given by two Pauli matrices and one identity
handle. The SL2 Weyl lift has square -I and remains distinct from its
negative; projective quotients must retain those rank-one lifts in the
ramification compatibility data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.RankTwoWordNormalization

open MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels
open MathlibExt.AlgebraicGeometry.TwistedRankTwoRepresentations
open scoped Matrix

def diagonalTwo : Matrix.GeneralLinearGroup (Fin 2) ℂ where
  val := !![2, 0; 0, 1]
  inv := !![1 / 2, 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def transvection : Matrix.GeneralLinearGroup (Fin 2) ℂ where
  val := !![1, 1; 0, 1]
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def orderedPair : Generators 1 → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  fun p => if p.snd = 0 then diagonalTwo else transvection

example : matrixWord orderedPair 0 1 = (1 / 2 : ℂ) := by
  have e : List.finRange 1 = [0] := by decide
  simp only [matrixWord, e, List.foldl_cons, List.foldl_nil]
  norm_num [orderedPair, diagonalTwo, transvection,
    Matrix.mul_apply, Fin.sum_univ_two]

def pauliA : Matrix.GeneralLinearGroup (Fin 2) ℂ where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def pauliB : Matrix.GeneralLinearGroup (Fin 2) ℂ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

def genusTwoTuple : Generators 2 → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  fun p => if p.fst = 0 then (if p.snd = 0 then pauliA else pauliB) else 1

example : matrixWord genusTwoTuple = minusGL ℂ := by
  have e : List.finRange 2 = [0, 1] := by decide
  simp only [matrixWord, e, List.foldl_cons, List.foldl_nil]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [genusTwoTuple, pauliA, pauliB, minusGL,
      Matrix.mul_apply, Fin.sum_univ_two]

example (m : Generators 0 → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    matrixWord m ≠ minusGL ℂ := by
  intro h
  have hc := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 2) ℂ => x 0 0) h
  norm_num [matrixWord, minusGL] at hc

example : ((weylMatrix ℂ * weylMatrix ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [weylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

example : (weylMatrix ℂ : Matrix (Fin 2) (Fin 2) ℂ) ≠ -weylMatrix ℂ := by
  intro h
  have hc := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  norm_num [weylMatrix] at hc

end MathlibExtTest.AlgebraicGeometry.RankTwoWordNormalization
