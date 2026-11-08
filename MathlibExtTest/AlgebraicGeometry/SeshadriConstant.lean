/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.SeshadriConstant
import Mathlib.Tactic

namespace MathlibExtTest.SeshadriConstant

open MathlibExt.AlgebraicGeometry.SeshadriConstant

example : monomialDegree (Finsupp.single (0 : Fin 2) 1) = 1 := by
  simp [monomialDegree]

example (a : AffinePoint) :
    multiplicity (MvPolynomial.X 0 - MvPolynomial.C (a 0)) a = 1 :=
  multiplicity_X_sub_C a

example (a : AffinePoint) :
    MathlibExt.AlgebraicGeometry.SeshadriConstant.multiplicity
      (1 : PlanePolynomial) a = 0 := by
  apply multiplicity_eq_zero_of_eval_ne_zero
  simp

example : 0 < MathlibExt.AlgebraicGeometry.SeshadriConstant.multiplicity
    (MvPolynomial.X (0 : Fin 2) : PlanePolynomial) 0 := by
  apply multiplicity_pos_of_eval_eq_zero
  · exact MvPolynomial.X_ne_zero 0
  · simp

example (x : Fin 10 → AffinePoint) : 0 ≤ affineSeshadriConstant x :=
  affineSeshadriConstant_nonneg x

example (x : Fin 10 → AffinePoint) : affineSeshadriConstant x ≤ 1 :=
  affineSeshadriConstant_le_one x

example : 0 ≤ seshadriConstant10 :=
  seshadriConstant10_nonneg

example : seshadriConstant10 ≤ 1 :=
  seshadriConstant10_le_one

end MathlibExtTest.SeshadriConstant
