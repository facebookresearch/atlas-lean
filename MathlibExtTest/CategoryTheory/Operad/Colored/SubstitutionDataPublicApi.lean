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

import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionData

/-!
# Focused O7E substitution-data public-contract packet

Pins the stable downstream-facing contracts for colored
substitution data: the outer and total profiles with their color
computations, the hom category with identity/composition
projections, the outer/total/inner functors with object and map
laws, and the factor family indices.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u

variable {Color : Type u}

-- The outer profile takes input colors from inner outputs.
example (d : ColoredSubstitutionData Color)
    (i : d.inner.index) :
    d.outerProfile.inputColor i = (d.inner.obj i).outputColor :=
  ColoredSubstitutionData.outerProfile_inputColor d i

-- The outer profile keeps the output color.
example (d : ColoredSubstitutionData Color) :
    d.outerProfile.outputColor = d.outputColor :=
  ColoredSubstitutionData.outerProfile_outputColor d

-- The total profile keeps the output color.
example (d : ColoredSubstitutionData Color) :
    d.totalProfile.outputColor = d.outputColor :=
  ColoredSubstitutionData.totalProfile_outputColor d

-- Identity homs act by identity on inner families.
example (d : ColoredSubstitutionData Color) :
    (𝟙 d : d ⟶ d).innerHom = 𝟙 d.inner :=
  ColoredSubstitutionData.id_innerHom d

-- Composition of homs acts by composition on inner families.
example {d e f : ColoredSubstitutionData Color} (p : d ⟶ e)
    (q : e ⟶ f) :
    (p ≫ q).innerHom = p.innerHom ≫ q.innerHom :=
  ColoredSubstitutionData.comp_innerHom p q

-- The outer-profile functor acts on objects.
example (d : ColoredSubstitutionData Color) :
    ColoredSubstitutionData.outerProfileFunctor.obj d =
      d.outerProfile :=
  ColoredSubstitutionData.outerProfileFunctor_obj d

-- Outer profile maps compose.
example {d e f : ColoredSubstitutionData Color} (p : d ⟶ e)
    (q : e ⟶ f) :
    ColoredSubstitutionData.outerProfileMap (p ≫ q) =
      ColoredSubstitutionData.outerProfileMap p ≫
        ColoredSubstitutionData.outerProfileMap q :=
  ColoredSubstitutionData.outerProfileMap_comp p q

-- The total-profile functor acts on objects.
example (d : ColoredSubstitutionData Color) :
    ColoredSubstitutionData.totalProfileFunctor.obj d =
      d.totalProfile :=
  ColoredSubstitutionData.totalProfileFunctor_obj d

-- Total profile maps respect identity.
example (d : ColoredSubstitutionData Color) :
    ColoredSubstitutionData.totalProfileMap (𝟙 d : d ⟶ d) =
      𝟙 d.totalProfile :=
  ColoredSubstitutionData.totalProfileMap_id d

-- Total profile maps respect composition.
example {d e f : ColoredSubstitutionData Color} (p : d ⟶ e)
    (q : e ⟶ f) :
    ColoredSubstitutionData.totalProfileMap (p ≫ q) =
      ColoredSubstitutionData.totalProfileMap p ≫
        ColoredSubstitutionData.totalProfileMap q :=
  ColoredSubstitutionData.totalProfileMap_comp p q
