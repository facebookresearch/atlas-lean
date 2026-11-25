/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralFoundationPackages
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Cameral source boundary regressions

The ramified dual-number fibre has a nonzero ideal symbol killed by
evaluation. The PGL2 root detects the equivariant value -1 whereas the
SL2 squared root equals +1. The actual nonzero nilpotent 2-by-2 matrix
has a two-dimensional centralizer, so regular-centralizer parameter
models must include it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExtTest.AlgebraicGeometry.CameralSourceNormalization

open MathlibExt.AlgebraicGeometry.CameralRamificationSymbols
open scoped TensorProduct Matrix

abbrev B := TrivSqZeroExt ℚ ℚ

def reflection : B ≃ₐ[ℚ] B where
  toFun x := TrivSqZeroExt.inl x.fst - TrivSqZeroExt.inr x.snd
  invFun x := TrivSqZeroExt.inl x.fst - TrivSqZeroExt.inr x.snd
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp [sub_add_sub_comm]
  map_mul' x y := by ext <;> simp [sub_eq_add_neg, add_comm]
  commutes' x := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

def epsilon : B := TrivSqZeroExt.inr 1

def epsilonSymbol : antiInvariant B reflection :=
  ⟨epsilon, by change reflection epsilon = -epsilon; ext <;> simp [reflection, epsilon]⟩

example : evaluation B reflection
    (epsilon ⊗ₜ[invariantAlgebra B reflection] epsilonSymbol) = 0 := by
  rw [evaluation_symbol]
  ext <;> simp [epsilon, epsilonSymbol]

theorem invariant_snd_zero (c : invariantAlgebra B reflection) : c.val.snd = 0 := by
  have h := congrArg TrivSqZeroExt.snd c.property
  have h' : -c.val.snd = c.val.snd := by simpa [reflection] using h
  linarith

def antiCoefficient : antiInvariant B reflection →ₗ[invariantAlgebra B reflection] B where
  toFun g := TrivSqZeroExt.inl g.val.snd
  map_add' g h := by ext <;> simp
  map_smul' c g := by
    change TrivSqZeroExt.inl ((c.val * g.val).snd) = c.val * TrivSqZeroExt.inl g.val.snd
    ext <;> simp [invariant_snd_zero c]

def symbolCoordinate : symbols B reflection →ₗ[B] B :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton B _ antiCoefficient)

example : epsilon ⊗ₜ[invariantAlgebra B reflection] epsilonSymbol ≠ 0 := by
  intro h
  have hc := congrArg symbolCoordinate h
  have hs := congrArg TrivSqZeroExt.snd hc
  norm_num [symbolCoordinate, antiCoefficient, epsilonSymbol, epsilon] at hs

def minusUnit : ℂˣ := Units.mk0 (-1) (by norm_num)

example : minusUnit⁻¹ = minusUnit := by ext; norm_num [minusUnit]
example : minusUnit ^ (2 : ℤ) = 1 := by ext; norm_num [minusUnit]
example : minusUnit ^ (1 : ℤ) ≠ 1 := by
  intro h
  have hv := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num [minusUnit] at hv

def nilpotent : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

example : nilpotent * nilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nilpotent, Matrix.mul_apply, Fin.sum_univ_two]

example : nilpotent ≠ 0 := by
  intro h
  have hv := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [nilpotent] at hv

example (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * nilpotent = nilpotent * M ↔ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  constructor
  · intro h
    have h00 := congrArg (fun K : Matrix (Fin 2) (Fin 2) ℂ => K 0 0) h
    have h01 := congrArg (fun K : Matrix (Fin 2) (Fin 2) ℂ => K 0 1) h
    simp [nilpotent, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    exact ⟨h00.symm, h01⟩
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nilpotent, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2]

end MathlibExtTest.AlgebraicGeometry.CameralSourceNormalization
