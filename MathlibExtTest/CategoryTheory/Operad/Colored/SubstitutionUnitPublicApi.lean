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

import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionUnit

/-!
# Focused O7E substitution-unit public-contract packet

Pins the stable downstream-facing contracts for unit substitution
data: the unary identity profile with color transport and color-map
naturality, the right/left unit substitution shapes with outer
profiles and canonical total homs, and the unit profile
isomorphisms with input-equivalence computations.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u

variable {Color : Type u}

-- A color path induces a unit-profile map.
example {c d : Color} (h : c = d) :
    ColoredSubstitutionData.unitProfile c ⟶
      ColoredSubstitutionData.unitProfile d :=
  ColoredSubstitutionData.unitProfileMap h

-- Unit profiles commute with color maps.
example {Color' : Type*} (f : Color → Color') (c : Color) :
    (ColoredSubstitutionData.unitProfile c).mapColors f =
      ColoredSubstitutionData.unitProfile (f c) :=
  ColoredSubstitutionData.unitProfile_mapColors f c

-- The right-unit shape substitutes unit profiles at every input.
example (P : ColoredProfile Color) :
    (ColoredSubstitutionData.rightUnit P).outputColor =
      P.outputColor :=
  rfl

-- The left-unit shape substitutes into the unit profile.
example (P : ColoredProfile Color) :
    (ColoredSubstitutionData.leftUnit P).outputColor =
      P.outputColor :=
  rfl

-- Right-unit outer homs are identities.
example (P : ColoredProfile Color) :
    ColoredSubstitutionData.rightUnitOuterHom P = 𝟙 P :=
  ColoredSubstitutionData.rightUnitOuterHom_eq_id P

-- Left-unit outer homs are identities.
example (P : ColoredProfile Color) :
    ColoredSubstitutionData.leftUnitOuterHom P =
      𝟙 (ColoredSubstitutionData.unitProfile P.outputColor) :=
  ColoredSubstitutionData.leftUnitOuterHom_eq_id P

-- The right-unit total iso exposes the sigma-PUnit equivalence.
example (P : ColoredProfile Color) :
    (ColoredSubstitutionData.rightUnitTotalIso P).hom.inputEquiv =
      Equiv.sigmaPUnit P.inputs :=
  ColoredSubstitutionData.rightUnitTotalIso_hom_inputEquiv P

-- The left-unit total iso exposes the sigma-unit equivalence.
example (P : ColoredProfile Color) :
    (ColoredSubstitutionData.leftUnitTotalIso P).hom.inputEquiv =
      (Equiv.sigmaEquivProd PUnit P.inputs).trans
        (Equiv.punitProd P.inputs) :=
  ColoredSubstitutionData.leftUnitTotalIso_hom_inputEquiv P
