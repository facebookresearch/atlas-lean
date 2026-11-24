/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Generators

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK

namespace MathlibExtTest.EnrichedDayGenerators

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

-- The three index types have no ordinary category or separator dictionary.
-- The base requires only a braid, and all object/Hom universes are independent.
example (a : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))] :
    EnrichedDayKernel.Generators.point T F G a =
      (λ_ ((F.externalTensor G).obj a)).inv ≫
        (eId V (T.obj a) ⊗ₘ 𝟙 ((F.externalTensor G).obj a)) ≫
        EnrichedDayKernel.gen T F G (T.obj a) a := rfl

example (a b : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj b))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj b))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj b))
      (EnrichedDayKernel.rightMap T F G (T.obj b))] :
    MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
        EnrichedDayKernel.Generators.point T F G b =
      (EnrichedDayKernel.Generators.point T F G a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
        (EnrichedDayKernel.obj T F G (T.obj a) ◁ T.map a b) ≫
        MonoidalClosed.uncurry (EnrichedDayKernel.Output.map T F G (T.obj a) (T.obj b)) :=
  EnrichedDayKernel.Generators.point_natural T F G a b

section ChosenFamily
variable
  [∀ k, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

example : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (F.externalTensor G) (T.comp V (EnrichedDayKernel.Output.functor T F G)) :=
  EnrichedDayKernel.Generators.transformation T F G

example (a : C × D) :
    (eHomEquiv V).symm ((EnrichedDayKernel.Generators.transformation T F G).app a) =
      EnrichedDayKernel.Generators.point T F G a :=
  EnrichedDayKernel.Generators.transformation_component T F G a
end ChosenFamily

section InputCharacteristics
variable {F' : EnrichedFunctor V C V} {G' : EnrichedFunctor V D V}

example
    (p : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
    (q : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G G') (a : C × D)
    [HasCoproduct (EnrichedDayKernel.relations T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F G (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G (T.obj a))
      (EnrichedDayKernel.rightMap T F G (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.relations T F' G' (T.obj a))]
    [HasCoproduct (EnrichedDayKernel.objects T F' G' (T.obj a))]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F' G' (T.obj a))
      (EnrichedDayKernel.rightMap T F' G' (T.obj a))] :
    EnrichedDayKernel.Generators.point T F G a ≫
        EnrichedDayKernel.Input.mapAt T p q (T.obj a) =
      ((eHomEquiv V).symm (p.app a.1) ⊗ₘ (eHomEquiv V).symm (q.app a.2)) ≫
        EnrichedDayKernel.Generators.point T F' G' a :=
  EnrichedDayKernel.Generators.point_input_natural T p q a

end InputCharacteristics

#check @EnrichedDayKernel.Generators.point_input_natural
#print axioms EnrichedDayKernel.Generators.point
#print axioms EnrichedDayKernel.Generators.point_natural
#print axioms EnrichedDayKernel.Generators.transformation
#print axioms EnrichedDayKernel.Generators.transformation_component
#print axioms EnrichedDayKernel.Generators.point_input_natural

end MathlibExtTest.EnrichedDayGenerators
