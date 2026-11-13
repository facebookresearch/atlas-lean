/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.LinearAlgebra.Matrix.PolynomialFunctionalCalculus

@[expose] public section

namespace MathlibExtTest.LinearAlgebra.Matrix.PolynomialFunctionalCalculus

open MetaMathlibExt

-- Algebra 379: Matrix-Valued Polynomial Functional Calculus

theorem matrixPolynomialEval_apply
    {m n : ℕ}
    (F : Matrix (Fin m) (Fin m) (Polynomial ℂ))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin m × Fin n) :
    matrixPolynomialEval F A i j =
      (Polynomial.eval₂
        (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ))
        A
        (F i.1 j.1))
        i.2 j.2 := by
  rfl

end MathlibExtTest.LinearAlgebra.Matrix.PolynomialFunctionalCalculus

end
