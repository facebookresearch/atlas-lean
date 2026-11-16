/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DeterminantZeroUnits
import Mathlib.Tactic.NormNum

/-! Zero-factor normalization retains nontrivial coefficients in the
actual exterior determinant and its inverse-dual factor. These maps
are used when scalar extension deletes degrees from a bounded complex.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.DeterminantZeroUnits

noncomputable section

set_option backward.isDefEq.respectTransparency false

private abbrev Z := ModuleCat.of ℤ (Fin 0 → ℤ)
private theorem hz : CategoryTheory.Limits.IsZero Z := ModuleCat.isZero_of_subsingleton _

example : zeroEquiv ℤ Z hz (scalarDeterminant ℤ Z hz 7) = 7 :=
  zeroEquiv_scalar ℤ Z hz 7

example :
    dualScalarEquiv ℤ ((zeroEquiv ℤ Z hz).symm.dualMap
      ((3 : ℤ) • (zeroEquiv ℤ Z hz).toLinearMap)) = (3 : ℤ) := by
  change (3 : ℤ) * zeroEquiv ℤ Z hz ((zeroEquiv ℤ Z hz).symm 1) = 3
  rw [LinearEquiv.apply_symm_apply, mul_one]

#print axioms MathlibExt.AlgebraicGeometry.DeterminantZeroUnits.termUnit
#print axioms MathlibExt.AlgebraicGeometry.DeterminantZeroUnits.removeZeroTerms
