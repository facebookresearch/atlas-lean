/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor

/-!
# Monoidal-functor tensor-power comparison tests

These compile-time tests pin the public orientation and naturality contract of
`mapTensorPowObjIso` for a generic strong monoidal functor.  They inspect the
forward and inverse morphisms rather than equality between bundled isomorphism
proof data.

No preservation result beyond finite tensor powers is tested here.
-/

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.MonoidalTensorPowerFunctor

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory.MonoidalCategory.TensorPower

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (G : Functor C D) [G.Monoidal]

section Computation

example (X : C) : tensorPowObj X 2 ≅ X ⊗ X :=
  tensorPowObjTwoIso X

#check @tensorPowObjHeadTailAddIso
#check @tensorPowObjHeadTailIso_eq_addIso
#check @tensorPowMap_comp_tensorPowObjHeadTailIso_hom
#check @tensorPowPrependMap
#check @tensorPowMap_comp_tensorPowPrependMap
#check @mapTensorPowObjIso_hom_eqToIso
#check @mapTensorPowObjIso_hom_headTail

#print axioms tensorPowMap_comp_tensorPowObjHeadTailIso_hom
#print axioms tensorPowPrependMap
#print axioms tensorPowMap_comp_tensorPowPrependMap

example (X : C) :
    (tensorPowObjTwoIso X).hom =
      (tensorPowObjOneIso X).hom ⊗ₘ 𝟙 X :=
  tensorPowObjTwoIso_hom X

example (X : C) :
    (tensorPowObjTwoIso X).inv =
      (tensorPowObjOneIso X).inv ⊗ₘ 𝟙 X :=
  tensorPowObjTwoIso_inv X

example (X : C) : X ⊗ (X ⊗ X) ≅ tensorPowObj X 3 :=
  tensorPowObjThreeRightIso X

example (X : C) :
    (tensorPowObjThreeRightIso X).hom =
      (associator X X X).inv ≫
        (((tensorPowObjOneIso X).inv ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) :=
  tensorPowObjThreeRightIso_hom_normalized X

-- At degree zero the forward map points from `G.obj (𝟙_ C)` to `𝟙_ D`.
example (X : C) :
    (mapTensorPowObjIso G X 0).hom =
      (Functor.Monoidal.εIso G).inv :=
  rfl

-- The inverse degree-zero map is the unit comparison of the monoidal functor.
example (X : C) :
    (mapTensorPowObjIso G X 0).inv =
      (Functor.Monoidal.εIso G).hom :=
  rfl

-- At a successor, the forward map first uses the inverse tensor comparison.
example (X : C) (n : ℕ) :
    (mapTensorPowObjIso G X (n + 1)).hom =
      (Functor.Monoidal.μIso G (tensorPowObj X n) X).inv ≫
        ((mapTensorPowObjIso G X n).hom ⊗ₘ 𝟙 (G.obj X)) :=
  rfl

-- The inverse successor map ends with the forward tensor comparison.
example (X : C) (n : ℕ) :
    (mapTensorPowObjIso G X (n + 1)).inv =
      ((mapTensorPowObjIso G X n).inv ⊗ₘ 𝟙 (G.obj X)) ≫
        (Functor.Monoidal.μIso G (tensorPowObj X n) X).hom :=
  rfl

end Computation

section Naturality

example (X : C) : tensorPowObj X 1 ≅ X :=
  tensorPowObjOneIso X

example {X Y : C} (f : X ⟶ Y) :
    tensorPowMap f 1 ≫ (tensorPowObjOneIso Y).hom =
      (tensorPowObjOneIso X).hom ≫ f :=
  tensorPowObjOneIso_hom_naturality f

example {X Y : C} (f : X ⟶ Y) :
    f ≫ (tensorPowObjOneIso Y).inv =
      (tensorPowObjOneIso X).inv ≫ tensorPowMap f 1 :=
  tensorPowObjOneIso_inv_naturality f

example {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    G.map (tensorPowMap f n) ≫ (mapTensorPowObjIso G Y n).hom =
      (mapTensorPowObjIso G X n).hom ≫ tensorPowMap (G.map f) n :=
  mapTensorPowObjIso_hom_naturality G f n

example (H : Functor C D) [H.Monoidal]
    (α : G ⟶ H) [NatTrans.IsMonoidal α] (X : C) (n : ℕ) :
    α.app (tensorPowObj X n) ≫ (mapTensorPowObjIso H X n).hom =
      (mapTensorPowObjIso G X n).hom ≫ tensorPowMap (α.app X) n :=
  mapTensorPowObjIso_hom_naturality_monoidal G H α X n

example (X : C) (m n : ℕ) :
    (mapTensorPowObjIso G X (m + n)).hom ≫
        (tensorPowObj_add (G.obj X) m n).hom =
      G.map (tensorPowObj_add X m n).hom ≫
        (Functor.Monoidal.μIso G
          (tensorPowObj X m) (tensorPowObj X n)).inv ≫
          ((mapTensorPowObjIso G X m).hom ⊗ₘ
            (mapTensorPowObjIso G X n).hom) :=
  mapTensorPowObjIso_hom_add G X m n

example (X : C) (n : ℕ) :
    (mapTensorPowObjIso G X (n + 2)).hom ≫
        (tensorPowObjHeadTailIso (G.obj X) n).hom =
      G.map (tensorPowObjHeadTailIso X n).hom ≫
        (Functor.Monoidal.μIso G X
          (tensorPowObj X (n + 1))).inv ≫
        (𝟙 (G.obj X) ⊗ₘ
          (mapTensorPowObjIso G X (n + 1)).hom) :=
  mapTensorPowObjIso_hom_headTail G X n

example (X : C) :
    (mapTensorPowObjIso G X 1).hom ≫
        (tensorPowObjOneIso (G.obj X)).hom =
      G.map (tensorPowObjOneIso X).hom :=
  mapTensorPowObjIso_hom_comp_tensorPowObjOneIso G X

end Naturality

end

end MathlibExtTest.MonoidalTensorPowerFunctor
