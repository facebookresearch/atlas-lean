/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.AdjointFamilyCells

set_option autoImplicit false
noncomputable section

universe w t s uC vC uD vD

open CategoryTheory HomotopicalAlgebra

namespace AdjointFamilyCellsTests

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {S : Type s} (L : S → C ⥤ D) (P : MorphismProperty C)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w}
    (fun (_ : T) => (MorphismProperty.adjointFamilyGenerators L P).homFamily) f)

example : RelativeCellComplex.{w}
    (fun (_ : T) (q : S × P.toSet) => (L q.1).map q.2.1.hom) f :=
  c.adjointFamilyCellTypes L P

example : (c.adjointFamilyCellTypes L P).F = c.F := c.adjointFamilyCellTypes_F L P

example (j : T) : (c.adjointFamilyCellTypes L P).incl.app j = c.incl.app j :=
  c.adjointFamilyCellTypes_incl L P j

#check @RelativeCellComplex.adjointFamilyCellTypes
#check @RelativeCellComplex.adjointFamilyCellTypes_F
#check @RelativeCellComplex.adjointFamilyCellTypes_incl
#print axioms RelativeCellComplex.adjointFamilyCellTypes
#print axioms RelativeCellComplex.adjointFamilyCellTypes_F
#print axioms RelativeCellComplex.adjointFamilyCellTypes_incl

end AdjointFamilyCellsTests
