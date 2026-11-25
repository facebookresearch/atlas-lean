/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensorPreserving

/-!
# Strong finite-tensor-preserving functors — public contract

Compile-time clients for identity comparison of finite families, the reduced-component
constructor for strong finite-tensor preservation, and the canonical identity-preserving value.
Identity and composition retain three independent category universes.
-/

@[expose] public section

open CategoryTheory

namespace MathlibExtTest.CategoryTheory.Monoidal.Unbiased.FiniteTensorPreservingPublicApi

universe uV vV uW vW uU vU

noncomputable section

variable {V : Type uV} {W : Type uW} {U : Type uU}
variable [Category.{vV} V] [Category.{vW} W] [Category.{vU} U]
variable [FiniteTensor V] [FiniteTensor W] [FiniteTensor U]

example : FiniteFamily.map (𝟭 V) ≅ 𝟭 (FiniteFamily V) :=
  FiniteFamily.mapIdIso V

example (X : FiniteFamily V) :
    (FiniteFamily.mapIdIso V).hom.app X = 𝟙 X :=
  FiniteFamily.mapIdIso_hom_app V X

example (X : FiniteFamily V) :
    (FiniteFamily.mapIdIso V).inv.app X = 𝟙 X :=
  FiniteFamily.mapIdIso_inv_app V X

example (F : V ⥤ W)
    (comparisonIso :
      FiniteFamily.map F ⋙ FiniteTensor.tensor (V := W) ≅
        FiniteTensor.tensor (V := V) ⋙ F)
    (singleton_hom : ∀ X : V,
      comparisonIso.hom.app ((FiniteFamily.singleton (C := V)).obj X) ≫
          F.map ((FiniteTensor.singletonIso (V := V)).hom.app X) =
        (FiniteTensor.singletonIso (V := W)).hom.app (F.obj X))
    (flatten_hom : ∀ X : FiniteFamily (FiniteFamily V),
      (FiniteTensor.flattenIso (V := W)).hom.app
            ((FiniteFamily.map (FiniteFamily.map F)).obj X) ≫
          (FiniteTensor.tensor (V := W)).map
            ((FiniteFamily.mapIso comparisonIso).hom.app X) ≫
          comparisonIso.hom.app
            ((FiniteFamily.map (FiniteTensor.tensor (V := V))).obj X) =
        comparisonIso.hom.app ((FiniteFamily.flatten (C := V)).obj X) ≫
          F.map ((FiniteTensor.flattenIso (V := V)).hom.app X)) :
    FiniteTensor.Preserving F :=
  FiniteTensor.Preserving.mkOfComponents comparisonIso singleton_hom flatten_hom

example : FiniteTensor.Preserving (𝟭 V) :=
  FiniteTensor.Preserving.id V

example (X : FiniteFamily V) :
    (FiniteTensor.Preserving.id V).comparisonIso.hom.app X = 𝟙 _ :=
  FiniteTensor.Preserving.id_comparisonIso_hom_app X

example (X : FiniteFamily V) :
    (FiniteTensor.Preserving.id V).comparisonIso.inv.app X = 𝟙 _ :=
  FiniteTensor.Preserving.id_comparisonIso_inv_app X

-- The identity comparison includes the nullary finite family without an inhabitant.
example :
    (FiniteTensor.Preserving.id V).comparisonIso.hom.app
        (FiniteFamily.empty : FiniteFamily V) = 𝟙 _ :=
  FiniteTensor.Preserving.id_comparisonIso_hom_app FiniteFamily.empty

example {F : V ⥤ W} {G : W ⥤ U}
    (p : FiniteTensor.Preserving F) (q : FiniteTensor.Preserving G) :
    FiniteTensor.Preserving (F ⋙ G) :=
  p.comp q

example {F : V ⥤ W} {G : W ⥤ U}
    (p : FiniteTensor.Preserving F) (q : FiniteTensor.Preserving G)
    (X : FiniteFamily V) :
    (p.comp q).comparisonIso.hom.app X =
      q.comparisonIso.hom.app ((FiniteFamily.map F).obj X) ≫
        G.map (p.comparisonIso.hom.app X) :=
  FiniteTensor.Preserving.comp_comparisonIso_hom_app p q X

example {F : V ⥤ W} {G : W ⥤ U}
    (p : FiniteTensor.Preserving F) (q : FiniteTensor.Preserving G)
    (X : FiniteFamily V) :
    (p.comp q).comparisonIso.inv.app X =
      G.map (p.comparisonIso.inv.app X) ≫
        q.comparisonIso.inv.app ((FiniteFamily.map F).obj X) :=
  FiniteTensor.Preserving.comp_comparisonIso_inv_app p q X

example (F : V ⥤ W) (p q : FiniteTensor.Preserving F)
    (h : p.comparisonIso = q.comparisonIso) : p = q :=
  FiniteTensor.Preserving.ext h

end

end MathlibExtTest.CategoryTheory.Monoidal.Unbiased.FiniteTensorPreservingPublicApi
