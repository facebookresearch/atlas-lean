/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExtTest.LinearAlgebra.Determinant.DependentPi
import MathlibExt.LinearAlgebra.Charpoly.DependentPi
import Mathlib.Tactic.NormNum

/-!
# Characteristic polynomial of a rank-one/rank-two product

The dependent product has eigenvalues 2, 3 and 5, so its characteristic
polynomial has constant coefficient -30, while its determinant is 30.
An empty product has characteristic polynomial one.
-/

@[expose] public section

noncomputable section
open Polynomial
namespace MathlibExtTest.DependentPi

theorem product_charpoly :
    productMap.charpoly = (X - C (2 : ℚ)) * ((X - C (3 : ℚ)) * (X - C (5 : ℚ))) := by
  rw [productMap, LinearMap.charpoly_pi_dependent]
  simp [componentMap, Matrix.charpoly_diagonal, Fin.prod_univ_two]

example : productMap.charpoly.coeff 0 = -30 := by
  norm_num [product_charpoly, Polynomial.coeff_mul]
example : productMap.det = 30 := product_det

example :
    (LinearMap.pi fun i : Fin 0 =>
      (LinearMap.id : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ)).comp (LinearMap.proj i)).charpoly = 1 := by
  rw [LinearMap.charpoly_pi_dependent]
  simp

end MathlibExtTest.DependentPi
