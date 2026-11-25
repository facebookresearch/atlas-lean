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

import MathlibExt.CategoryTheory.Operad.OperadObj.Hom

/-!
# Focused O7E operad-morphism public-contract packet

Pins the stable downstream-facing contracts for morphisms of
enriched operads: the factor/source homs with identity and
composition laws, morphism extensionality, identity and
composition with their underlying maps, the category structure,
the forgetful functor with faithfulness, and the forward/inverse
morphisms from a collection isomorphism.

The full isomorphism lifting is pinned separately in
`IsoOfCollectionIsoPublicApi`.
-/

open CategoryTheory
open CategoryTheory.Operad

universe v u

variable {V : Type u} [Category.{v} V] [FiniteTensor V]

-- Factor hom signature.
noncomputable example {O P : SymmetricCollection V} (α : O ⟶ P)
    (X : SubstitutionData) :
    (substitutionFactors O).obj X ⟶ (substitutionFactors P).obj X :=
  OperadObj.HomData.factorHom α X

-- Source hom signature.
noncomputable example {O P : SymmetricCollection V} (α : O ⟶ P)
    (X : SubstitutionData) :
    (FiniteTensor.tensor (V := V)).obj
          ((substitutionFactors O).obj X) ⟶
      (FiniteTensor.tensor (V := V)).obj
        ((substitutionFactors P).obj X) :=
  OperadObj.HomData.sourceHom α X

-- Identity laws.
example (O : SymmetricCollection V) (X : SubstitutionData) :
    OperadObj.HomData.factorHom (V := V) (𝟙 O) X =
      𝟙 ((substitutionFactors O).obj X) :=
  OperadObj.HomData.factorHom_id O X

example (O : SymmetricCollection V) (X : SubstitutionData) :
    OperadObj.HomData.sourceHom (V := V) (𝟙 O) X = 𝟙 _ :=
  OperadObj.HomData.sourceHom_id O X

-- Composition laws.
example {O P Q : SymmetricCollection V} (α : O ⟶ P)
    (β : P ⟶ Q) (X : SubstitutionData) :
    OperadObj.HomData.factorHom (V := V) (α ≫ β) X =
      (OperadObj.HomData.factorHom (V := V) α X).comp
        (OperadObj.HomData.factorHom (V := V) β X) :=
  OperadObj.HomData.factorHom_comp α β X

example {O P Q : SymmetricCollection V} (α : O ⟶ P)
    (β : P ⟶ Q) (X : SubstitutionData) :
    OperadObj.HomData.sourceHom (V := V) (α ≫ β) X =
      OperadObj.HomData.sourceHom (V := V) α X ≫
        OperadObj.HomData.sourceHom (V := V) β X :=
  OperadObj.HomData.sourceHom_comp α β X

-- Morphism extensionality.
example {O P : OperadObj V} {F G : OperadObj.Hom O P}
    (h : F.toCollectionHom = G.toCollectionHom) : F = G :=
  OperadObj.Hom.ext h

-- Identity and composition with underlying maps.
noncomputable example (O : OperadObj V) : OperadObj.Hom O O :=
  OperadObj.Hom.id O

noncomputable example {O P Q : OperadObj V}
    (F : OperadObj.Hom O P) (G : OperadObj.Hom P Q) :
    OperadObj.Hom O Q :=
  F.comp G

example (O : OperadObj V) :
    (OperadObj.Hom.id (V := V) O).toCollectionHom =
      (𝟙 O.toCollection : O.toCollection ⟶ O.toCollection) :=
  OperadObj.Hom.id_toCollectionHom O

example {O P Q : OperadObj V} (F : OperadObj.Hom O P)
    (G : OperadObj.Hom P Q) :
    (F.comp G).toCollectionHom =
      (F.toCollectionHom ≫ G.toCollectionHom :
        O.toCollection ⟶ Q.toCollection) :=
  OperadObj.Hom.comp_toCollectionHom F G

-- Category structure and forgetful functor.
example : Category (OperadObj V) := inferInstance

noncomputable example : OperadObj V ⥤ SymmetricCollection V :=
  OperadObj.forget

example : (OperadObj.forget (V := V)).Faithful := inferInstance

-- Forward/inverse morphisms from a collection isomorphism.
noncomputable example {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    O ⟶ P :=
  OperadObj.homOfCollectionIso e mapUnit mapSubst

noncomputable example {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    P ⟶ O :=
  OperadObj.invHomOfCollectionIso e mapUnit mapSubst

example {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (OperadObj.homOfCollectionIso e mapUnit mapSubst).toCollectionHom =
      e.hom :=
  OperadObj.homOfCollectionIso_toCollectionHom e mapUnit mapSubst

example {O P : OperadObj V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : O.unit ≫ e.hom.app ⟨arityOne⟩ = P.unit)
    (mapSubst : ∀ X,
      O.subst.app X ≫ e.hom.app ⟨substitutionTotalObj X⟩ =
        OperadObj.HomData.sourceHom e.hom X ≫ P.subst.app X) :
    (OperadObj.invHomOfCollectionIso e mapUnit mapSubst).toCollectionHom =
      e.inv :=
  OperadObj.invHomOfCollectionIso_toCollectionHom e mapUnit mapSubst
