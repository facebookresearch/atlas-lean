/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMultiplicationNaturality

/-! # Tests for parameter naturality of core biproduct multiplication -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe v u

namespace MathlibExtTest.CategoryTheory.Limits.CoreBiproductMultiplicationNaturality

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check coreLeftBiprodBiprodIso_parameter_naturality_component
#check coreLeftBiprodBiprodIso_parameter_naturality

example {A A' B B' : C} (e : A ≅ A') (d : B ≅ B') :
    coreLeftBiprodIsoOfIso (biprod.mapIso e d) ≪≫
        coreLeftBiprodBiprodIso A' B' =
      coreLeftBiprodBiprodIso A B ≪≫
        Functor.isoWhiskerRight (coreLeftBiprodIsoOfIso d)
          (coreLeftBiprodFunctor A) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor B')
          (coreLeftBiprodIsoOfIso e) :=
  coreLeftBiprodBiprodIso_parameter_naturality e d

/-- Boundary case: both parameter isomorphisms are identities. -/
example (A B : C) :
    coreLeftBiprodIsoOfIso
          (biprod.mapIso (Iso.refl A) (Iso.refl B)) ≪≫
        coreLeftBiprodBiprodIso A B =
      coreLeftBiprodBiprodIso A B ≪≫
        Functor.isoWhiskerRight (coreLeftBiprodIsoOfIso (Iso.refl B))
          (coreLeftBiprodFunctor A) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor B)
          (coreLeftBiprodIsoOfIso (Iso.refl A)) :=
  coreLeftBiprodBiprodIso_parameter_naturality
    (Iso.refl A) (Iso.refl B)

/-- Boundary case: parameter naturality at two zero parameters. -/
example :
    coreLeftBiprodIsoOfIso
          (biprod.mapIso (Iso.refl (0 : C)) (Iso.refl (0 : C))) ≪≫
        coreLeftBiprodBiprodIso (0 : C) (0 : C) =
      coreLeftBiprodBiprodIso (0 : C) (0 : C) ≪≫
        Functor.isoWhiskerRight
          (coreLeftBiprodIsoOfIso (Iso.refl (0 : C)))
          (coreLeftBiprodFunctor (0 : C)) ≪≫
        Functor.isoWhiskerLeft (coreLeftBiprodFunctor (0 : C))
          (coreLeftBiprodIsoOfIso (Iso.refl (0 : C))) :=
  coreLeftBiprodBiprodIso_parameter_naturality
    (Iso.refl (0 : C)) (Iso.refl (0 : C))

#print axioms coreLeftBiprodBiprodIso_parameter_naturality_component
#print axioms coreLeftBiprodBiprodIso_parameter_naturality

end MathlibExtTest.CategoryTheory.Limits.CoreBiproductMultiplicationNaturality

end
