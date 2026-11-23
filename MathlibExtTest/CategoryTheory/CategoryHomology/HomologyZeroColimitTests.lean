/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.CategoryHomology.HomologyZeroColimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology

universe uJ vJ uA vA

#check coefficientHomologyClass_map
#print axioms coefficientHomologyClass_map
#check coefficientHomologyCocone
#print axioms coefficientHomologyCocone
#check coefficientHomologyCoconeIsColimit
#print axioms coefficientHomologyCoconeIsColimit
#check coefficientHomologyZeroColimitIso
#print axioms coefficientHomologyZeroColimitIso
#check coefficientHomologyZeroColimitIso_class
#print axioms coefficientHomologyZeroColimitIso_class
#check coefficientHomologyZeroColimitIso_naturality
#print axioms coefficientHomologyZeroColimitIso_naturality

namespace HomologyZeroColimitTests

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasCoproducts.{max uJ vJ} A]
  {M N : J ⥤ A}

noncomputable example : IsColimit (coefficientHomologyCocone M) := coefficientHomologyCoconeIsColimit M

example [HasColimit M] (j : J) :
    coefficientHomologyClass M j ≫ (coefficientHomologyZeroColimitIso M).hom = colimit.ι M j :=
  coefficientHomologyZeroColimitIso_class M j

example [HasColimit M] [HasColimit N] (α : M ⟶ N) :
    (homologyWithCoefficientsFunctor (C := J) (A := A) 0).map α ≫
        (coefficientHomologyZeroColimitIso N).hom =
      (coefficientHomologyZeroColimitIso M).hom ≫ colimMap α :=
  coefficientHomologyZeroColimitIso_naturality α

end HomologyZeroColimitTests
