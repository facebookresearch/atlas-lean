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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Hom

/-!
# Focused O7E colored operad-morphism public-contract packet

Pins the stable downstream-facing contracts for morphisms of
enriched colored operads: the factor/source homs with identity
and composition laws, morphism extensionality, identity and
composition with their underlying maps, the category structure,
the forgetful functor with faithfulness, and the isomorphism
lifting from a collection isomorphism.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V] [FiniteTensor V]

-- Factor hom signature.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionFactors O).obj d ⟶
      (ColoredOperadObj.substitutionFactors P).obj d :=
  ColoredOperadObj.HomData.factorHom α d

-- Source hom signature.
noncomputable example {O P : ColoredSymmetricCollection Color V}
    (α : O ⟶ P) (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionSource O).obj d ⟶
      (ColoredOperadObj.substitutionSource P).obj d :=
  ColoredOperadObj.HomData.sourceHom α d

-- Identity laws.
example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.factorHom (𝟙 O) d =
      𝟙 ((ColoredOperadObj.substitutionFactors O).obj d) :=
  ColoredOperadObj.HomData.factorHom_id O d

example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.sourceHom (𝟙 O) d = 𝟙 _ :=
  ColoredOperadObj.HomData.sourceHom_id O d

-- Composition laws.
example {O P Q : ColoredSymmetricCollection Color V} (α : O ⟶ P)
    (β : P ⟶ Q) (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.factorHom (α ≫ β) d =
      (ColoredOperadObj.HomData.factorHom α d).comp
        (ColoredOperadObj.HomData.factorHom β d) :=
  ColoredOperadObj.HomData.factorHom_comp α β d

example {O P Q : ColoredSymmetricCollection Color V} (α : O ⟶ P)
    (β : P ⟶ Q) (d : ColoredSubstitutionData Color) :
    ColoredOperadObj.HomData.sourceHom (α ≫ β) d =
      ColoredOperadObj.HomData.sourceHom α d ≫
        ColoredOperadObj.HomData.sourceHom β d :=
  ColoredOperadObj.HomData.sourceHom_comp α β d

-- Morphism extensionality.
example {O P : ColoredOperadObj Color V}
    {F G : ColoredOperadObj.Hom O P}
    (h : F.toCollectionHom = G.toCollectionHom) : F = G :=
  ColoredOperadObj.Hom.ext h

-- Identity and composition with underlying maps.
noncomputable example (O : ColoredOperadObj Color V) :
    ColoredOperadObj.Hom O O :=
  ColoredOperadObj.Hom.id O

noncomputable example {O P Q : ColoredOperadObj Color V}
    (F : ColoredOperadObj.Hom O P)
    (G : ColoredOperadObj.Hom P Q) :
    ColoredOperadObj.Hom O Q :=
  ColoredOperadObj.Hom.comp F G

example (O : ColoredOperadObj Color V) :
    (ColoredOperadObj.Hom.id O).toCollectionHom = 𝟙 O.toCollection :=
  ColoredOperadObj.Hom.id_toCollectionHom O

example {O P Q : ColoredOperadObj Color V}
    (F : ColoredOperadObj.Hom O P)
    (G : ColoredOperadObj.Hom P Q) :
    (ColoredOperadObj.Hom.comp F G).toCollectionHom =
      F.toCollectionHom ≫ G.toCollectionHom :=
  ColoredOperadObj.Hom.comp_toCollectionHom F G

-- Category structure and forgetful functor.
example : Category (ColoredOperadObj Color V) := inferInstance

noncomputable example :
    ColoredOperadObj Color V ⥤ ColoredSymmetricCollection Color V :=
  ColoredOperadObj.forget

example : (ColoredOperadObj.forget (Color := Color) (V := V)).Faithful :=
  inferInstance

-- Forward/inverse morphisms from a collection isomorphism.
noncomputable example {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) =
        P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        ColoredOperadObj.HomData.sourceHom e.hom d ≫ P.subst.app d) :
    O ⟶ P :=
  ColoredOperadObj.homOfCollectionIso e mapUnit mapSubst

noncomputable example {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) =
        P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        ColoredOperadObj.HomData.sourceHom e.hom d ≫ P.subst.app d) :
    P ⟶ O :=
  ColoredOperadObj.invHomOfCollectionIso e mapUnit mapSubst

-- Isomorphism lifting and its projections.
noncomputable example {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) =
        P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        ColoredOperadObj.HomData.sourceHom e.hom d ≫ P.subst.app d) :
    O ≅ P :=
  ColoredOperadObj.isoOfCollectionIso e mapUnit mapSubst

example {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) =
        P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        ColoredOperadObj.HomData.sourceHom e.hom d ≫ P.subst.app d) :
    ((ColoredOperadObj.isoOfCollectionIso e mapUnit mapSubst).hom).toCollectionHom
      = e.hom :=
  ColoredOperadObj.isoOfCollectionIso_hom_toCollectionHom
    e mapUnit mapSubst

example {O P : ColoredOperadObj Color V}
    (e : O.toCollection ≅ P.toCollection)
    (mapUnit : ∀ c,
      O.unit c ≫ e.hom.app (ColoredSubstitutionData.unitProfile c) =
        P.unit c)
    (mapSubst : ∀ d,
      O.subst.app d ≫ e.hom.app d.totalProfile =
        ColoredOperadObj.HomData.sourceHom e.hom d ≫ P.subst.app d) :
    ((ColoredOperadObj.isoOfCollectionIso e mapUnit mapSubst).inv).toCollectionHom
      = e.inv :=
  ColoredOperadObj.isoOfCollectionIso_inv_toCollectionHom
    e mapUnit mapSubst
