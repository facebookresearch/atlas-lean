/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CentralScalar

import Mathlib.Tactic.NormNum.Prime
#check @groupCohomology.isZero_H0_of_central_smul
#check @groupCohomology.isZero_H1_of_central_smul
#check @Matrix.GeneralLinearGroup.stdRep
#check @Matrix.GeneralLinearGroup.stdRep_apply
#check @Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep
#check @Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep_zmod

-- `H¹(GL₂(𝔽₅), 𝔽₅²) = 0`.
example : CategoryTheory.Limits.IsZero
    (groupCohomology.H1 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 2) (ZMod 5)))) :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  (Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep_zmod 5 (by norm_num)).2

-- Over `ℚ`, `H⁰` and `H¹` of `GL₃(ℚ)` on `ℚ³` vanish.
example : CategoryTheory.Limits.IsZero
      (groupCohomology.H0 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 3) ℚ))) ∧
    CategoryTheory.Limits.IsZero
      (groupCohomology.H1 (Rep.of (Matrix.GeneralLinearGroup.stdRep (Fin 3) ℚ))) :=
  Matrix.GeneralLinearGroup.isZero_H0_and_H1_stdRep (Fin 3) ℚ (by norm_num)
