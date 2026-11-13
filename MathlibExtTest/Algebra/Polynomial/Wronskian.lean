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

public import MathlibExt.Algebra.Polynomial.Wronskian

@[expose] public section

namespace MathlibExtTest.Algebra.Polynomial.Wronskian

open MetaMathlibExt

-- Analysis 406: Wronskian of a Finite Family of Polynomials

theorem polynomialWronskian_singleton
    {R : Type*}
    [CommRing R]
    (P : Polynomial R) :
    polynomialWronskian (fun _ : Fin 1 => P) = P := by
  unfold polynomialWronskian
  change
    Matrix.det
        (fun i j : Fin 1 =>
          (Polynomial.derivativeFinsupp P) (j : ℕ)) =
      P
  calc
    Matrix.det
        (fun i j : Fin 1 =>
          (Polynomial.derivativeFinsupp P) (j : ℕ))
        =
      (Polynomial.derivativeFinsupp P) 0 := by
        simpa using
          (Matrix.det_fin_one
            (fun i j : Fin 1 =>
              (Polynomial.derivativeFinsupp P) (j : ℕ)))
    _ = P := by
      simp [Polynomial.derivativeFinsupp_apply_apply]

end MathlibExtTest.Algebra.Polynomial.Wronskian

end
