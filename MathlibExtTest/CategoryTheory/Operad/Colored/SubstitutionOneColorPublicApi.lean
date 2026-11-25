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

import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionOneColor

/-!
# Focused O7E one-color substitution-data public-contract packet

Pins the stable downstream-facing contracts comparing ordinary and
one-colored substitution data: the back-and-forth functors, the unit
and counit isomorphisms, the triangle identity, and the equivalence.
-/

open CategoryTheory
open CategoryTheory.Operad

universe c

-- Back-and-forth functors.
noncomputable example :
    SubstitutionData ⥤ ColoredSubstitutionData PUnit :=
  ColoredSubstitutionData.oneColorFunctor

noncomputable example :
    ColoredSubstitutionData PUnit ⥤ SubstitutionData :=
  ColoredSubstitutionData.forgetOneColorFunctor

-- Object computation of the forward functor.
example (d : SubstitutionData) :
    (ColoredSubstitutionData.oneColorFunctor.obj d).inner.index =
      d.index :=
  ColoredSubstitutionData.oneColorFunctor_obj_inner_index.{c} d

example (d : SubstitutionData) (i : d.index) :
    (ColoredSubstitutionData.oneColorFunctor.obj d).inner.obj i =
      ColoredProfile.oneColorFunctor.obj (d.obj i) :=
  ColoredSubstitutionData.oneColorFunctor_obj_inner_obj d i

example (d : SubstitutionData) :
    (ColoredSubstitutionData.oneColorFunctor.obj d).outerProfile =
      ColoredProfile.oneColorFunctor.obj ⟨d.index⟩ :=
  ColoredSubstitutionData.oneColorFunctor_obj_outerProfile d

example (d : SubstitutionData) :
    (ColoredSubstitutionData.oneColorFunctor.obj d).totalProfile =
      ColoredProfile.oneColorFunctor.obj ⟨substitutionTotalObj d⟩ :=
  ColoredSubstitutionData.oneColorFunctor_obj_totalProfile d

-- Unit iso and its identity components.
noncomputable example :
    𝟭 SubstitutionData ≅
      ColoredSubstitutionData.oneColorFunctor ⋙
        ColoredSubstitutionData.forgetOneColorFunctor :=
  ColoredSubstitutionData.oneColorUnitIso

example (d : SubstitutionData) :
    ColoredSubstitutionData.oneColorUnitIso.hom.app d = 𝟙 d :=
  ColoredSubstitutionData.oneColorUnitIso_hom_app.{c} d

example (d : SubstitutionData) :
    ColoredSubstitutionData.oneColorUnitIso.inv.app d = 𝟙 d :=
  ColoredSubstitutionData.oneColorUnitIso_inv_app.{c} d

-- Counit maps and iso.
noncomputable example (d : ColoredSubstitutionData PUnit) :
    (ColoredSubstitutionData.forgetOneColorFunctor ⋙
      ColoredSubstitutionData.oneColorFunctor).obj d ⟶ d :=
  ColoredSubstitutionData.oneColorCounitHom d

noncomputable example (d : ColoredSubstitutionData PUnit) :
    d ⟶ (ColoredSubstitutionData.forgetOneColorFunctor ⋙
      ColoredSubstitutionData.oneColorFunctor).obj d :=
  ColoredSubstitutionData.oneColorCounitInv d

noncomputable example (d : ColoredSubstitutionData PUnit) :
    (ColoredSubstitutionData.forgetOneColorFunctor ⋙
      ColoredSubstitutionData.oneColorFunctor).obj d ≅ d :=
  ColoredSubstitutionData.oneColorCounitIsoApp d

noncomputable example :
    ColoredSubstitutionData.forgetOneColorFunctor ⋙
        ColoredSubstitutionData.oneColorFunctor ≅
      𝟭 (ColoredSubstitutionData PUnit) :=
  ColoredSubstitutionData.oneColorCounitIso

-- Triangle identity.
example (d : SubstitutionData) :
    ColoredSubstitutionData.oneColorFunctor.map
          (ColoredSubstitutionData.oneColorUnitIso.hom.app d) ≫
        ColoredSubstitutionData.oneColorCounitIso.hom.app
          (ColoredSubstitutionData.oneColorFunctor.obj d) =
      𝟙 _ :=
  ColoredSubstitutionData.oneColor_triangle d

-- The equivalence and its projections.
noncomputable example :
    SubstitutionData ≌ ColoredSubstitutionData PUnit :=
  ColoredSubstitutionData.oneColorEquivalence

example :
    ColoredSubstitutionData.oneColorEquivalence.functor =
      ColoredSubstitutionData.oneColorFunctor :=
  ColoredSubstitutionData.oneColorEquivalence_functor

example :
    ColoredSubstitutionData.oneColorEquivalence.inverse =
      ColoredSubstitutionData.forgetOneColorFunctor :=
  ColoredSubstitutionData.oneColorEquivalence_inverse

example :
    ColoredSubstitutionData.oneColorEquivalence.unitIso =
      ColoredSubstitutionData.oneColorUnitIso :=
  ColoredSubstitutionData.oneColorEquivalence_unitIso

example :
    ColoredSubstitutionData.oneColorEquivalence.counitIso =
      ColoredSubstitutionData.oneColorCounitIso :=
  ColoredSubstitutionData.oneColorEquivalence_counitIso
