/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Adjunction.SourceHomColimit

set_option autoImplicit false
noncomputable section
universe t vT vC vD uC uD

open CategoryTheory Limits Opposite

namespace MathlibExtTest.AdjointSourceHomColimit

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {T : Type t} [Category.{vT} T] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (A : C) (F : T ⥤ D)
  [PreservesColimit F R]
  [PreservesColimit (F ⋙ R) (coyoneda.obj (op A))]

-- Actual arbitrary caller cocone and source object, with no global colimit class.
example (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((coyoneda.obj (op (L.obj A))).mapCocone c) :=
  adj.isColimitLeftAdjointSource A F c hc

example [HasColimit F] :
    IsColimit ((coyoneda.obj (op (L.obj A))).mapCocone (colimit.cocone F)) :=
  adj.isColimitLeftAdjointSource A F (colimit.cocone F) (colimit.isColimit F)

example : PreservesColimit F (coyoneda.obj (op (L.obj A))) :=
  adj.preservesColimit_leftAdjointSource A F

-- Truly independent source and target Hom universes in both directions.
section LowerSourceHom
variable {C0 : Type 2} [Category.{0} C0] {D1 : Type 3} [Category.{1} D1]
  {L01 : C0 ⥤ D1} {R10 : D1 ⥤ C0}
  (a01 : L01 ⊣ R10) (A0 : C0) (E1 : T ⥤ D1)
  [PreservesColimit E1 R10]
  [PreservesColimit (E1 ⋙ R10) (coyoneda.obj (op A0))]
example : PreservesColimit E1 (coyoneda.obj (op (L01.obj A0))) :=
  a01.preservesColimit_leftAdjointSource A0 E1
end LowerSourceHom

section HigherSourceHom
variable {C1 : Type 3} [Category.{1} C1] {D0 : Type 2} [Category.{0} D0]
  {L10 : C1 ⥤ D0} {R01 : D0 ⥤ C1}
  (a10 : L10 ⊣ R01) (A1 : C1) (E0 : T ⥤ D0)
  [PreservesColimit E0 R01]
  [PreservesColimit (E0 ⋙ R01) (coyoneda.obj (op A1))]
example : PreservesColimit E0 (coyoneda.obj (op (L10.obj A1))) :=
  a10.preservesColimit_leftAdjointSource A1 E0
end HigherSourceHom

#check @Adjunction.preservesColimit_leftAdjointSource
#check @Adjunction.isColimitLeftAdjointSource
#print axioms Adjunction.preservesColimit_leftAdjointSource
#print axioms Adjunction.isColimitLeftAdjointSource

end MathlibExtTest.AdjointSourceHomColimit
