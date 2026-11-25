/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorBraidingCoherence

/-!
# Public clients of the global derived monoidal and closed stack

All four structures are inferred on the actual chosen homotopy category.
The tensor and internal-Hom examples keep the original Q/R functors and
their full covariant and contravariant arrow functions.
-/

noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open HomotopicalAlgebra HomotopicalAlgebra.DerivedTensorConstructions
open scoped MonoidalClosed

namespace MathlibExtTest.DerivedClosedStructure

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C))

local notation "H" => MonoidalHo d

example : MonoidalCategory H := inferInstance
example : BraidedCategory H := inferInstance
example : SymmetricCategory H := inferInstance
example : MonoidalClosed H := inferInstance

example (X Y : H) : (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

example {X Y Z : H} (f : X ⊗ Y ⟶ Z) :
    MonoidalClosed.uncurry (MonoidalClosed.curry f) = f :=
  MonoidalClosed.uncurry_curry f

example (X Y Z : H) (f : Y ⟶ (ihom X).obj Z) :
    MonoidalClosed.curry (MonoidalClosed.uncurry f) = f :=
  MonoidalClosed.curry_uncurry f

example (X : H) : tensorLeft X = (tensor d).obj X :=
  MonoidalHo.tensorLeft_eq d X

example (X : H) : ihom X = (derivedInternalHom d).obj (op X) :=
  MonoidalHo.ihom_eq d X

example (X Y Z : H) (f : X ⊗ Y ⟶ Z) :
    MonoidalClosed.curry f = DerivedTensorAdjunction.homEquiv d X Y Z f :=
  MonoidalHo.curry_eq d X Y Z f

example (X : H) {Y Z : H} (f : Y ⟶ Z) :
    (ihom X).map f = ((derivedInternalHom d).obj (op X)).map f :=
  MonoidalHo.ihom_map_eq d X f

example {X Y : H} (f : X ⟶ Y) :
    MonoidalClosed.pre f = (derivedInternalHom d).map f.op :=
  MonoidalHo.ihom_pre_eq d f

example {X Y : Hᵒᵖ} (f : X ⟶ Y) :
    (MonoidalClosed.internalHom (C := H)).map f = (derivedInternalHom d).map f :=
  MonoidalHo.internalHom_map_eq d f

end MathlibExtTest.DerivedClosedStructure
