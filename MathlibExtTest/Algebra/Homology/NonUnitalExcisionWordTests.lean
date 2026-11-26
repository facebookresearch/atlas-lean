/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.NaiveFiltrationComplex
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Tactic.FinCases

/-!
# Noncommutative ideal words over a ring with zero divisors

The proper two-sided ideal `M₂(Z/6Z) × {0}` in `M₂(Z/6Z) × Z/6Z` gives a
three-letter word with two ideal entries and one quotient entry. Its first
two Hochschild faces vanish, while its cyclic last face is nonzero. The
signed boundary therefore retains the cyclic product in its original order.
The next boundary is computed to be zero. Multiplying this nonzero boundary
by two keeps it nonzero, whereas multiplying that result by three kills it.
-/

noncomputable section

open scoped TensorProduct BigOperators
open ModuleCat.Algebra.Hochschild.NonUnital

namespace MathlibExtTest.NonUnitalExcisionWords

private abbrev R := ZMod 6
private abbrev Mat := Matrix (Fin 2) (Fin 2) R
private abbrev A := Mat × R

private def firstIdeal : NonUnitalSubalgebra R A where
  carrier := {a | a.2 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a.2 + b.2 = 0
    change a.2 = 0 at ha
    change b.2 = 0 at hb
    rw [ha, hb, zero_add]
  mul_mem' := by
    intro a b ha hb
    change a.2 * b.2 = 0
    change a.2 = 0 at ha
    rw [ha, zero_mul]
  smul_mem' := by
    intro r a ha
    change r • a.2 = 0
    change a.2 = 0 at ha
    rw [ha, smul_zero]

private instance : firstIdeal.IsTwoSided where
  mul_mem_left a {x} hx := by
    change a.2 * x.2 = 0
    change x.2 = 0 at hx
    rw [hx, mul_zero]
  mul_mem_right {x} hx a := by
    change x.2 * a.2 = 0
    change x.2 = 0 at hx
    rw [hx, zero_mul]

private def e01 : A := (Matrix.single 0 1 (1 : R), 0)
private def e10 : A := (Matrix.single 1 0 (1 : R), 0)
private def e11 : A := (Matrix.single 1 1 (1 : R), 0)
private def q : A := (0, 1)

private def letters : Fin 3 → A := ![e01, q, e10]
private def outputLetters : Fin 2 → A := ![e11, q]
private def word : TensorPower R 3 A := PiTensorProduct.tprod R letters
private def outputWord : TensorPower R 2 A := PiTensorProduct.tprod R outputLetters

private theorem face_zero : regularWordFace R A 1 (0 : Fin 3) word = 0 := by
  rw [word, regularWordFace_castSucc_tprod R A 1 (0 : Fin 2)]
  have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent (0 : Fin 2) letters =
      ![0, e10] := by decide
  rw [h]
  exact (PiTensorProduct.tprod R).map_coord_zero (0 : Fin 2) rfl

private theorem face_one : regularWordFace R A 1 (1 : Fin 3) word = 0 := by
  rw [word, regularWordFace_castSucc_tprod R A 1 (1 : Fin 2)]
  have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent (1 : Fin 2) letters =
      ![e01, 0] := by decide
  rw [h]
  exact (PiTensorProduct.tprod R).map_coord_zero (1 : Fin 2) rfl

private theorem face_last : regularWordFace R A 1 (2 : Fin 3) word = outputWord := by
  rw [word, regularWordFace_last_tprod]
  apply congrArg (PiTensorProduct.tprod R)
  decide

private theorem boundary_word : regularWordBoundary R A 1 word = outputWord := by
  simp [regularWordBoundary_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    Fin.sum_univ_three, face_zero, face_one, face_last]

private def entry11 : A →ₗ[R] R where
  toFun a := a.1 1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def quotientCoordinate : A →ₗ[R] R := LinearMap.snd R Mat R

private def evaluateTwo : TensorPower R 2 A →ₗ[R] R :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra R (Fin 2) R).compLinearMap
      ![entry11, quotientCoordinate])

private theorem evaluate_output : evaluateTwo outputWord = 1 := by
  simp [evaluateTwo, outputWord, outputLetters, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    Fin.prod_univ_two, entry11, quotientCoordinate, e11, q]

private theorem next_boundary : regularWordBoundary R A 0 outputWord = 0 := by
  have h0 : regularWordFace R A 0 (0 : Fin 2) outputWord = 0 := by
    rw [outputWord, regularWordFace_castSucc_tprod R A 0 (0 : Fin 1)]
    have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent
        (0 : Fin 1) outputLetters = ![0] := by decide
    rw [h]
    exact (PiTensorProduct.tprod R).map_coord_zero (0 : Fin 1) rfl
  have h1 : regularWordFace R A 0 (1 : Fin 2) outputWord = 0 := by
    rw [outputWord, regularWordFace_last_tprod]
    have h : ModuleCat.Algebra.Hochschild.hochschildMulAdjacent (0 : Fin 1)
        (fun i => outputLetters ((finRotate 2).symm i)) = ![0] := by decide
    rw [h]
    exact (PiTensorProduct.tprod R).map_coord_zero (0 : Fin 1) rfl
  simp [regularWordBoundary_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    Fin.sum_univ_two, h0, h1]

example : e01 * e10 ≠ e10 * e01 := by decide

example : regularWordFace R A 1 (0 : Fin 3) word = 0 := face_zero

example : regularWordFace R A 1 (1 : Fin 3) word = 0 := face_one

example : regularWordFace R A 1 (2 : Fin 3) word = outputWord := face_last

example : regularWordBoundary R A 1 word = outputWord := boundary_word

example : regularWordBoundary R A 1 word ≠ 0 := by
  intro h
  have hvalue := congrArg evaluateTwo h
  rw [boundary_word, evaluate_output, map_zero] at hvalue
  exact (by decide : (1 : R) ≠ 0) hvalue

example : regularWordBoundary R A 0 (regularWordBoundary R A 1 word) = 0 := by
  rw [boundary_word, next_boundary]

example : evaluateTwo (regularWordBoundary R A 1 ((2 : R) • word)) = 2 := by
  rw [map_smul, boundary_word, map_smul, evaluate_output]
  exact mul_one 2

example : regularWordBoundary R A 1 ((2 : R) • word) ≠ 0 := by
  intro h
  have hvalue := congrArg evaluateTwo h
  rw [map_smul, boundary_word, map_smul, evaluate_output, map_zero] at hvalue
  change (2 : R) = 0 at hvalue
  exact (by decide : (2 : R) ≠ 0) hvalue

example : (3 : R) • regularWordBoundary R A 1 ((2 : R) • word) = 0 := by
  rw [map_smul, smul_smul, show (3 : R) * 2 = 0 from by decide, zero_smul]

private theorem word_mem_stage : word ∈ idealWordSpan R A firstIdeal 3 2 := by
  apply Submodule.subset_span
  refine ⟨letters, ?_, rfl⟩
  classical
  have h : Finset.univ.filter (fun i : Fin 3 => letters i ∈ firstIdeal.toSubmodule) =
      {0, 2} := by
    ext i
    fin_cases i <;> simp [letters, firstIdeal, e01, e10, q]
  unfold idealEntryCount
  rw [h]
  decide

example : word ∈ idealWordSpan R A firstIdeal 3 2 := word_mem_stage

example : regularWordBoundary R A 1 word ∈ idealWordSpan R A firstIdeal 2 1 := by
  apply idealWordSpan_regularWordBoundary R A firstIdeal 1 2
  exact ⟨word, word_mem_stage, rfl⟩

end MathlibExtTest.NonUnitalExcisionWords
