/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.SmallObject.DiagramEligibility

set_option autoImplicit false
noncomputable section

universe w uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace DiagramEligibilityTests

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  (P : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [OrderBot κ.ord.ToType] [Small.{w} J] [LocallySmall.{w} J]
  (hP : P.IsCardinalForSmallObjectArgument κ)

example : (MorphismProperty.adjointFamilyGenerators
    (fun j : J => evaluationLeftAdjoint C j) P).IsCardinalForSmallObjectArgument κ :=
  isCardinalForSmallObjectArgument_freeDiagrams (J := J) P κ hP

example : LocallySmall.{w} (J ⥤ C) :=
  (isCardinalForSmallObjectArgument_freeDiagrams (J := J) P κ hP).locallySmall

example : HasIterationOfShape κ.ord.ToType (J ⥤ C) :=
  (isCardinalForSmallObjectArgument_freeDiagrams (J := J) P κ hP).hasIterationOfShape

example {A B X Y : J ⥤ C} (i : A ⟶ B)
    (hi : MorphismProperty.adjointFamilyGenerators
      (fun j : J => evaluationLeftAdjoint C j) P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun (_ : κ.ord.ToType) =>
      (MorphismProperty.adjointFamilyGenerators
        (fun j : J => evaluationLeftAdjoint C j) P).homFamily) f) :
    PreservesColimit c.F (coyoneda.obj (Opposite.op A)) :=
  (isCardinalForSmallObjectArgument_freeDiagrams (J := J) P κ hP).preservesColimit i hi f c

#check @isCardinalForSmallObjectArgument_freeDiagrams
#print axioms isCardinalForSmallObjectArgument_freeDiagrams

end DiagramEligibilityTests
