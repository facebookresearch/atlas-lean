/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductTriangle

/-!
# Zero-first-parameter triangle for core biproduct translation

The multiplication comparison with zero as its first parameter is compatible
with the zero-unit comparison.  At an object `X`, the component equality is

```text
  α(0, B, X).hom ≫ snd = biprod.map snd (𝟙 X).
```

Both occurrences of `snd` are the appropriate forward zero-unit maps.  The
proof uses biproduct extensionality and the defining projection laws of the
forward associator.  No pentagon, zero-comma transport, or bundled action is
asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory ZeroObject

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Underlying biproduct component equation for the zero-first-parameter
triangle. -/
theorem coreLeftBiprodBiprodIso_leftUnit_component
    (B X : C) :
    (biprod.associator (0 : C) B X).hom ≫
        (isoZeroBiprod (isZero_zero C)).symm.hom =
      biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X) := by
  apply biprod.hom_ext <;>
    simp [biprod.associator]

/-- Multiplication with zero as the first parameter followed by zero
elimination agrees with changing that parameter along the left zero unitor. -/
theorem coreLeftBiprodBiprodIso_leftUnit (B : C) :
    coreLeftBiprodBiprodIso (0 : C) B ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor B)
          coreLeftBiprodZeroIso ≪≫
        Functor.rightUnitor (coreLeftBiprodFunctor B) =
      coreLeftBiprodIsoOfIso
        (isoZeroBiprod (isZero_zero C)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Core.hom_ext
  change
    (biprod.associator (0 : C) B X.of).hom ≫
          (isoZeroBiprod (isZero_zero C)).symm.hom ≫ 𝟙 _ =
      biprod.map (isoZeroBiprod (isZero_zero C)).symm.hom (𝟙 X.of)
  rw [Category.comp_id]
  exact coreLeftBiprodBiprodIso_leftUnit_component B X.of

end CategoryTheory.Limits

end
