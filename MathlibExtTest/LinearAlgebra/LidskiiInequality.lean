/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.WeylEigenvalueSum
import MathlibExt.LinearAlgebra.LidskiiInequality

open MathlibExt.LinearAlgebra.LidskiiInequalityWanted.LinearAlgebra

-- The endpoint p = 1 gives the total absolute displacement bound.
example {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      ∑ j, |(hB.sub hA).eigenvalues₀ j| := by
  simpa only [Real.rpow_one] using lidskii_inequality hA hB (_hp := le_rfl)

-- A scalar shift of the zero matrix has repeated eigenvalues and attains the bound.
example :
    let hA : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := Matrix.isHermitian_zero
    let hB : (1 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := Matrix.isHermitian_one
    ∑ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ^ (3 / 2 : ℝ) = 2 := by
  intro hA hB
  have hscalar (x : ℝ) (j : Fin (Fintype.card (Fin 2))) :
      (Matrix.isHermitian_diagonal_of_self_adjoint (fun _ : Fin 2 => (x : ℂ))
        (by ext i; simp)).eigenvalues₀ j = x :=
    Matrix.IsHermitian.eigenvalues₀_diagonal_of_antitone (fun _ _ _ => le_rfl) j
  have ha (j : Fin (Fintype.card (Fin 2))) : hA.eigenvalues₀ j = 0 := by
    simpa only [Complex.ofReal_zero, Matrix.diagonal_zero] using hscalar 0 j
  have hb (j : Fin (Fintype.card (Fin 2))) : hB.eigenvalues₀ j = 1 := by
    simpa only [Complex.ofReal_one, Matrix.diagonal_one] using hscalar 1 j
  have hdiff (j : Fin (Fintype.card (Fin 2))) : (hB.sub hA).eigenvalues₀ j = 1 := by
    simpa only [sub_zero] using hb j
  have hp : 1 ≤ (3 / 2 : ℝ) := by norm_num
  have h := lidskii_inequality hA hB (_hp := hp)
  simp only [hdiff, abs_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_fin, Nat.cast_ofNat] at h
  refine le_antisymm h ?_
  simp [ha, hb]
