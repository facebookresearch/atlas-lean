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

import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionAssociativity

/-!
# Focused O7E substitution-associativity public-contract packet

Pins the stable downstream-facing contracts for three-level
substitution data: the middle, outer-after-inner, and flattened
inner two-level data with inner-family computations, color-map
naturality of each projection, the outer/total profile
identification, and the canonical total isomorphism with its
sigma-associativity input equivalence.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u

variable {Color : Type u} {Color' : Type*}

-- Middle data keeps branch outer profiles.
example (d : ColoredAssocData Color) (i : d.branches.index) :
    d.middleData.inner.obj i = (d.localData i).outerProfile :=
  d.middleData_inner_obj i

-- Outer-after-inner data keeps branch total profiles.
example (d : ColoredAssocData Color) (i : d.branches.index) :
    d.outerAfterInnerData.inner.obj i =
      (d.localData i).totalProfile :=
  d.outerAfterInnerData_inner_obj i

-- Flattened inner data keeps the innermost profiles.
example (d : ColoredAssocData Color) (i : d.branches.index)
    (j : (d.localData i).inner.index) :
    d.innerData.inner.obj ⟨i, j⟩ =
      (d.localData i).inner.obj j :=
  d.innerData_inner_obj i j

-- The flat outer profile is the middle total profile.
example (d : ColoredAssocData Color) :
    d.innerData.outerProfile = d.middleData.totalProfile :=
  d.innerData_outerProfile

-- Color maps commute with the middle projection.
example (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).middleData = d.middleData.mapColors f :=
  ColoredAssocData.mapColors_middleData f d

-- Color maps commute with the outer-after-inner projection.
example (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).outerAfterInnerData =
      d.outerAfterInnerData.mapColors f :=
  ColoredAssocData.mapColors_outerAfterInnerData f d

-- Color maps commute with the flattened inner projection.
example (f : Color → Color') (d : ColoredAssocData Color) :
    (d.mapColors f).innerData = d.innerData.mapColors f :=
  ColoredAssocData.mapColors_innerData f d

-- The total iso exposes sigma-associativity on inputs.
example (d : ColoredAssocData Color) :
    d.totalIso.hom.inputEquiv = Equiv.sigmaAssoc
      (fun (i : d.branches.index)
        (j : (d.localData i).inner.index) =>
        ((d.localData i).inner.obj j).inputs) :=
  d.totalIso_hom_inputEquiv

-- The total hom commutes with color maps.
example (f : Color → Color') (d : ColoredAssocData Color) :
    d.totalHom.mapColors f = (d.mapColors f).totalHom :=
  d.totalHom_mapColors f
