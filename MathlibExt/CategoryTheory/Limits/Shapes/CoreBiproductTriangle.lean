/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMultiplicationNaturality

/-!
# Right-unit triangle for core biproduct translation

The multiplication comparison for left-biproduct translation is compatible
with its zero-unit comparison.  At an object `X`, the triangle is the explicit
biproduct identity

```text
  α(A, 0, X) ≫ (𝟙 A ⊞ snd) = (fst ⊞ 𝟙 X).
```

It is proved by biproduct extensionality and the defining projection laws for
`biprod.associator` and `biprod.map`.  This file contains only the right-unit
triangle; no left-unit companion, pentagon, transported zero-comma law, or
bundled action is asserted.
-/

@[expose] public section

noncomputable section

open CategoryTheory ZeroObject

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Underlying biproduct component equation for the right-unit triangle. -/
theorem coreLeftBiprodBiprodIso_rightUnit_component
    (A X : C) :
    (biprod.associator A (0 : C) X).hom ≫
        biprod.map (𝟙 A)
          (isoZeroBiprod (isZero_zero C)).symm.hom =
      biprod.map (isoBiprodZero (isZero_zero C)).symm.hom (𝟙 X) := by
  apply biprod.hom_ext <;>
    simp [biprod.associator, Category.assoc]

/-- Multiplication by the zero parameter followed by zero elimination agrees
with changing the parameter along the right zero unitor. -/
theorem coreLeftBiprodBiprodIso_rightUnit (A : C) :
    coreLeftBiprodBiprodIso A (0 : C) ≪≫
        Functor.isoWhiskerRight coreLeftBiprodZeroIso
          (coreLeftBiprodFunctor A) ≪≫
        Functor.leftUnitor (coreLeftBiprodFunctor A) =
      coreLeftBiprodIsoOfIso
        (isoBiprodZero (isZero_zero C)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Core.hom_ext
  change
    (biprod.associator A (0 : C) X.of).hom ≫
          biprod.map (𝟙 A)
            (isoZeroBiprod (isZero_zero C)).symm.hom ≫ 𝟙 _ =
      biprod.map (isoBiprodZero (isZero_zero C)).symm.hom (𝟙 X.of)
  rw [Category.comp_id]
  exact coreLeftBiprodBiprodIso_rightUnit_component A X.of

end CategoryTheory.Limits

end
