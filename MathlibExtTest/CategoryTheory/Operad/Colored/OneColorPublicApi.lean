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

import MathlibExt.CategoryTheory.Operad.Colored.OneColor

/-!
# Focused O7E one-color public-contract packet

Pins the stable downstream-facing contracts for the one-color
translation: the profile functor and its forgetful inverse with
object/map computations, the unit/counit isomorphisms with their
component projections, the forget-after-counit computation, the
triangle law, and the equivalence projections.
-/

open CategoryTheory
open CategoryTheory.Operad

-- One-color profiles keep the arity as inputs.
example (X : FinBijGroupoid) :
    (ColoredProfile.oneColorFunctor.{0}.obj X).inputs = X.of :=
  ColoredProfile.oneColorFunctor_obj_inputs.{0} X

-- One-color maps expose the underlying equivalence.
example {X Y : FinBijGroupoid} (f : X ⟶ Y) :
    (ColoredProfile.oneColorFunctor.{0}.map f).inputEquiv =
      FinBijGroupoid.equivOfHom f :=
  ColoredProfile.oneColorFunctor_map_inputEquiv.{0} f

-- Forgetting keeps the inputs.
example (P : ColoredProfile PUnit.{1}) :
    (ColoredProfile.forgetOneColorFunctor.{0}.obj P).of = P.inputs :=
  ColoredProfile.forgetOneColorFunctor_obj.{0} P

-- Forgetting exposes the input equivalence.
example {P Q : ColoredProfile PUnit.{1}} (f : P ⟶ Q) :
    FinBijGroupoid.equivOfHom
        (ColoredProfile.forgetOneColorFunctor.{0}.map f) =
      f.inputEquiv :=
  ColoredProfile.forgetOneColorFunctor_map.{0} f

-- The unit iso forward components are identities.
example (X : FinBijGroupoid) :
    ColoredProfile.oneColorUnitIso.{0}.hom.app X = 𝟙 _ :=
  ColoredProfile.oneColorUnitIso_hom_app.{0} X

-- The unit iso inverse components are identities.
example (X : FinBijGroupoid) :
    ColoredProfile.oneColorUnitIso.{0}.inv.app X = 𝟙 _ :=
  ColoredProfile.oneColorUnitIso_inv_app.{0} X

-- The counit iso forward components are the counit homs.
example (P : ColoredProfile PUnit.{1}) :
    ColoredProfile.oneColorCounitIso.{0}.hom.app P =
      ColoredProfile.oneColorCounitHom.{0} P :=
  ColoredProfile.oneColorCounitIso_hom_app.{0} P

-- Forgetting colors sends the counit hom to the identity.
example (P : ColoredProfile PUnit.{1}) :
    ColoredProfile.forgetOneColorFunctor.{0}.map
          (ColoredProfile.oneColorCounitHom.{0} P) =
      𝟙 (ColoredProfile.forgetOneColorFunctor.{0}.obj P) :=
  ColoredProfile.forgetOneColorFunctor_map_oneColorCounitHom.{0} P

-- The counit iso inverse components are groupoid inverses.
example (P : ColoredProfile PUnit.{1}) :
    ColoredProfile.oneColorCounitIso.{0}.inv.app P =
      Groupoid.inv (ColoredProfile.oneColorCounitHom.{0} P) :=
  ColoredProfile.oneColorCounitIso_inv_app.{0} P

-- The triangle law for the one-color equivalence.
example (X : FinBijGroupoid) :
    ColoredProfile.oneColorFunctor.{0}.map
          (ColoredProfile.oneColorUnitIso.{0}.hom.app X) ≫
        ColoredProfile.oneColorCounitIso.{0}.hom.app
          (ColoredProfile.oneColorFunctor.{0}.obj X) = 𝟙 _ :=
  ColoredProfile.oneColor_triangle.{0} X

-- The equivalence projects to the profile functor.
example : ColoredProfile.oneColorEquivalence.{0}.functor =
    ColoredProfile.oneColorFunctor.{0} :=
  ColoredProfile.oneColorEquivalence_functor.{0}

-- The equivalence projects to the forgetful functor.
example : ColoredProfile.oneColorEquivalence.{0}.inverse =
    ColoredProfile.forgetOneColorFunctor.{0} :=
  ColoredProfile.oneColorEquivalence_inverse.{0}
