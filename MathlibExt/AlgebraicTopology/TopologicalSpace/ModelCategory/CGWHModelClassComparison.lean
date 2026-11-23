/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelClasses

/-!
# Comparison of CGWH model classes with TopCat

The three selected CGWH morphism properties are created in two stages:
first along the inclusion into compactly generated spaces and then along
the inclusion into topological spaces. This file identifies each staged
inverse image with the inverse image along the composite underlying functor.

No fourth class facade, factorization, model-category instance, or Quillen
result is introduced here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MorphismProperty

universe u v

namespace CGWH

/-- CGWH weak homotopy equivalences are exactly the inverse image of TopCat
weak homotopy equivalences along the composite inclusion. -/
theorem weakHomotopyEquivalences_eq_inverseImage :
    weakHomotopyEquivalences.{u, v} =
      TopCat.weakHomotopyEquivalences.{v}.inverseImage
        cgwhToTop.{u, v} := by
  rfl

/-- CGWH model cofibrations are exactly the inverse image of the selected
TopCat cofibrations along the composite inclusion. -/
theorem modelCofibrations_eq_inverseImage :
    modelCofibrations.{u, v} =
      TopCat.realizedBoundaryInclusions.{v}.rlp.llp.inverseImage
        cgwhToTop.{u, v} := by
  rfl

/-- CGWH model fibrations are exactly the inverse image of the selected
TopCat fibrations along the composite inclusion. -/
theorem modelFibrations_eq_inverseImage :
    modelFibrations.{u, v} =
      TopCat.realizedHornInclusions.{v}.rlp.inverseImage
        cgwhToTop.{u, v} := by
  rfl

end CGWH
