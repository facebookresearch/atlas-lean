/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClassComparison

/-!
# Tests for direct CGWH-to-TopCat model-class comparisons

These owners exercise both equality orientations, membership through the
composite inclusion, all universe pairs, and the absence of a selected
CGWH model-category instance.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace MathlibExtTest.CGWHModelClassComparison

#check @CGWH.weakHomotopyEquivalences_eq_inverseImage
#check @CGWH.modelCofibrations_eq_inverseImage
#check @CGWH.modelFibrations_eq_inverseImage

section Symbolic

variable {X Y : CGWH.{u, v}} (f : X ⟶ Y)

example : CGWH.weakHomotopyEquivalences.{u, v} =
    TopCat.weakHomotopyEquivalences.{v}.inverseImage
      CGWH.cgwhToTop.{u, v} :=
  CGWH.weakHomotopyEquivalences_eq_inverseImage

example : TopCat.weakHomotopyEquivalences.{v}.inverseImage
    CGWH.cgwhToTop.{u, v} =
      CGWH.weakHomotopyEquivalences.{u, v} :=
  CGWH.weakHomotopyEquivalences_eq_inverseImage.symm

example : CGWH.modelCofibrations.{u, v} =
    TopCat.realizedBoundaryInclusions.{v}.rlp.llp.inverseImage
      CGWH.cgwhToTop.{u, v} :=
  CGWH.modelCofibrations_eq_inverseImage

example : TopCat.realizedBoundaryInclusions.{v}.rlp.llp.inverseImage
    CGWH.cgwhToTop.{u, v} = CGWH.modelCofibrations.{u, v} :=
  CGWH.modelCofibrations_eq_inverseImage.symm

example : CGWH.modelFibrations.{u, v} =
    TopCat.realizedHornInclusions.{v}.rlp.inverseImage
      CGWH.cgwhToTop.{u, v} :=
  CGWH.modelFibrations_eq_inverseImage

example : TopCat.realizedHornInclusions.{v}.rlp.inverseImage
    CGWH.cgwhToTop.{u, v} = CGWH.modelFibrations.{u, v} :=
  CGWH.modelFibrations_eq_inverseImage.symm

example : CGWH.weakHomotopyEquivalences f ↔
    TopCat.weakHomotopyEquivalences (CGWH.cgwhToTop.map f) := by
  rw [CGWH.weakHomotopyEquivalences_eq_inverseImage]
  rfl

example : CGWH.modelCofibrations f ↔
    TopCat.realizedBoundaryInclusions.rlp.llp
      (CGWH.cgwhToTop.map f) := by
  rw [CGWH.modelCofibrations_eq_inverseImage]
  rfl

example : CGWH.modelFibrations f ↔
    TopCat.realizedHornInclusions.rlp
      (CGWH.cgwhToTop.map f) := by
  rw [CGWH.modelFibrations_eq_inverseImage]
  rfl

example : True := by
  fail_if_success
    let _ : HomotopicalAlgebra.ModelCategory CGWH.{u, v} := inferInstance
  trivial

end Symbolic

section UniverseMatrix

#check @CGWH.weakHomotopyEquivalences_eq_inverseImage.{0, 0}
#check @CGWH.modelCofibrations_eq_inverseImage.{0, 0}
#check @CGWH.modelFibrations_eq_inverseImage.{0, 0}

#check @CGWH.weakHomotopyEquivalences_eq_inverseImage.{1, 1}
#check @CGWH.modelCofibrations_eq_inverseImage.{1, 1}
#check @CGWH.modelFibrations_eq_inverseImage.{1, 1}

#check @CGWH.weakHomotopyEquivalences_eq_inverseImage.{0, 1}
#check @CGWH.modelCofibrations_eq_inverseImage.{0, 1}
#check @CGWH.modelFibrations_eq_inverseImage.{0, 1}

#check @CGWH.weakHomotopyEquivalences_eq_inverseImage.{1, 0}
#check @CGWH.modelCofibrations_eq_inverseImage.{1, 0}
#check @CGWH.modelFibrations_eq_inverseImage.{1, 0}

end UniverseMatrix

#print axioms CGWH.weakHomotopyEquivalences_eq_inverseImage
#print axioms CGWH.modelCofibrations_eq_inverseImage
#print axioms CGWH.modelFibrations_eq_inverseImage

end MathlibExtTest.CGWHModelClassComparison
