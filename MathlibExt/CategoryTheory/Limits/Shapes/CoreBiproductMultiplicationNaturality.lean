/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.Whiskering
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMultiplication

/-!
# Parameter naturality of core biproduct multiplication

The forward-associator comparison

```text
  K (A ⊞ B) ≅ K B ⋙ K A
```

is natural when both fixed summands are changed by isomorphisms.  On an
object `X`, the square is exactly `biprod.associator_natural e.hom d.hom
(𝟙 X.of)`.  The two successive parameter changes on the iterated-translation
side are first combined by biproduct extensionality.

No unit triangle, pentagon, transported zero-comma law, or bundled action is
asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasBinaryBiproducts C]

/-- Underlying component equation for parameter naturality of core
left-biproduct multiplication. -/
theorem coreLeftBiprodBiprodIso_parameter_naturality_component
    {A A' B B' : C} (e : A ≅ A') (d : B ≅ B') (X : Core C) :
    biprod.map (biprod.map e.hom d.hom) (𝟙 X.of) ≫
        (biprod.associator A' B' X.of).hom =
      (biprod.associator A B X.of).hom ≫
        biprod.map (𝟙 A) (biprod.map d.hom (𝟙 X.of)) ≫
        biprod.map e.hom (𝟙 (B' ⊞ X.of)) := by
  have hMap :
      biprod.map e.hom (biprod.map d.hom (𝟙 X.of)) =
        biprod.map (𝟙 A) (biprod.map d.hom (𝟙 X.of)) ≫
          biprod.map e.hom (𝟙 (B' ⊞ X.of)) := by
    apply biprod.hom_ext <;> simp
  rw [biprod.associator_natural e.hom d.hom (𝟙 X.of), hMap]

/-- Changing both parameters before applying multiplication agrees with
applying multiplication first and then changing the two iterated-translation
parameters. -/
theorem coreLeftBiprodBiprodIso_parameter_naturality
    {A A' B B' : C} (e : A ≅ A') (d : B ≅ B') :
    coreLeftBiprodIsoOfIso (biprod.mapIso e d) ≪≫
        coreLeftBiprodBiprodIso A' B' =
      coreLeftBiprodBiprodIso A B ≪≫
        Functor.isoWhiskerRight (coreLeftBiprodIsoOfIso d)
          (coreLeftBiprodFunctor A) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor B')
          (coreLeftBiprodIsoOfIso e) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Core.hom_ext
  exact coreLeftBiprodBiprodIso_parameter_naturality_component e d X

end CategoryTheory.Limits

end
