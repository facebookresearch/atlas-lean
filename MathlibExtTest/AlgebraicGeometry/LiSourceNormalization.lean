/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LogarithmicMapDerivations
import MathlibExt.AlgebraicGeometry.LiTensorEvaluation
import MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
At an ordinary zero smoothing parameter, the actual first-order change
of the parameter is allowed. Imposing the full logarithmic equation on
that parameter would force it to vanish. Tensor evaluation also retains
nonflat coefficient modules. The torus point is an actual nilpotent unit.
-/

noncomputable section
open Polynomial
open MathlibExt.AlgebraicGeometry.LogarithmicMapDerivations
open MathlibExt.AlgebraicGeometry.LiTensorEvaluation
open scoped TensorProduct

private abbrev atZero : ℚ[X] →+* ℚ := evalRingHom 0

local instance polyAlgebra : Algebra ℚ[X] ℚ := atZero.toAlgebra

local instance polyTower : IsScalarTower ℚ ℚ[X] ℚ :=
  IsScalarTower.of_algebraMap_eq' (by ext q; simp)

private def smoothingDerivative : Derivation ℚ ℚ[X] ℚ where
  toLinearMap := lcoeff ℚ 1
  map_one_eq_zero' := by
    change (1 : ℚ[X]).coeff 1 = 0
    rw [← C_1, coeff_C]
    norm_num
  leibniz' p q := by
    change (p * q).coeff 1 = p • q.coeff 1 + q • p.coeff 1
    simp only [Algebra.smul_def]
    change (p * q).coeff 1 = p.eval 0 * q.coeff 1 + q.eval 0 * p.coeff 1
    simp only [← coeff_zero_eq_eval_zero, coeff_mul, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, Finset.map_singleton]
    norm_num
    ring

example : smoothingDerivative.toLinearMap ∈ ordinary (k := ℚ) (A := ℚ)
    (fun _ : Fin 1 => X) (LinearMap.id : ℚ →ₗ[ℚ] ℚ) := by
  constructor
  · exact ⟨smoothingDerivative, rfl⟩
  · intro i; exact ⟨smoothingDerivative X, rfl⟩

example : ¬ ∃ eta : ℚ, smoothingDerivative X = (X : ℚ[X]) • eta := by
  rintro ⟨eta, h⟩
  change (X : ℚ[X]).coeff 1 = (atZero X) * eta at h
  norm_num [atZero] at h

example : evaluation ℤ ℤ (ZMod 2) ((2 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)) (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = 0 := by
  rw [evaluation_tmul]
  change (2 : ℤ) • (1 : ZMod 2) = 0
  rw [zsmul_eq_mul]
  simpa using ZMod.natCast_self 2

example :
    (MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints.unit ℚ (3 : ℚ)).val.fst = 1 ∧
    (MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints.unit ℚ (3 : ℚ)).val.snd = 3 := by
  constructor <;> norm_num [MathlibExt.AlgebraicGeometry.TorusInfinitesimalPoints.unit]
