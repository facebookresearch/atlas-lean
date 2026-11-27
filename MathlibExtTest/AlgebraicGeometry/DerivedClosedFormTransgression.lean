/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression
import Mathlib.Algebra.TrivSqZeroExt.Basic

open CategoryTheory CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedClosedFormTransgression

namespace DerivedClosedFormTransgressionTest
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Dual := TrivSqZeroExt ℚ ℚ
def epsilon : Dual := TrivSqZeroExt.inr 1

-- The source term is nonzero only in degree -9; the target is nonzero only in degree -12.
def sourceComplex : GlobalComplex Dual := (liftComplex Dual).obj ((𝟙_ (Cochains Dual))⟦(9 : ℤ)⟧)
def targetComplex : GlobalComplex Dual := sourceComplex⟦(3 : ℤ)⟧

def traceDegreeThree : sourceComplex ⟶ targetComplex⟦-3⟧ :=
  (shiftFunctorZero (GlobalComplex Dual) ℤ).inv.app sourceComplex ≫
    (shiftFunctorAdd' (GlobalComplex Dual) (3 : ℤ) (-3) 0 (by omega)).hom.app sourceComplex

def sourceVertex : (sourceComplex⟦-9⟧).X 0 :=
  (sourceComplex.shiftFunctorObjXIso (-9) 0 (-9) (by omega)).inv
    (ULift.up.{1} (shiftedUnit (9 : ℤ) epsilon))

def targetCoefficient (x : (targetComplex⟦-12⟧).X 0) : Dual :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat Dual))).hom
    ((CochainComplex.shiftFunctorObjXIso (𝟙_ (Cochains Dual)) 9 (-9) 0 (by omega)).hom
      (((sourceComplex.shiftFunctorObjXIso 3 (-12) (-9) (by omega)).hom
        ((targetComplex.shiftFunctorObjXIso (-12) 0 (-12) (by omega)).hom x)).down))

-- n=-7, p=2, d=3: the actual map lands in closed degree -10 and cochain degree -12.
example : targetCoefficient
    (((shiftIntegrationCochain traceDegreeThree 2 (-7)).f 0).hom sourceVertex) = epsilon := by
  rfl

example : targetCoefficient
    (((shiftIntegrationCochain traceDegreeThree 2 (-7)).f 0).hom sourceVertex) ≠ 0 := by
  change epsilon ≠ 0
  intro h
  have h' := congrArg TrivSqZeroExt.snd h
  norm_num [epsilon] at h'

example : targetCoefficient
    (((shiftIntegrationCochain traceDegreeThree 2 (-7)).f 0).hom sourceVertex) ^ 2 = 0 := by
  change epsilon ^ 2 = 0
  simp [epsilon, pow_two]

end
end DerivedClosedFormTransgressionTest
