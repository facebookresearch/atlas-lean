/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Output

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonoidalClosed

set_option autoImplicit false

noncomputable section

universe uC uD uK uV vV uI vI

section PlainRectangularIndices

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

-- The source index needs only its enrichment; all three index universes are independent.
example : EnrichedFunctor V K V := EnrichedDayKernel.Output.functor T F G

example (k : K) :
    (EnrichedDayKernel.Output.functor T F G).obj k =
      EnrichedDayKernel.obj T F G k := rfl

-- This is a whole enriched hom object, with the actual integrand action on every generator.
example (k k' : K) (a : C × D) :
    (β_ (k ⟶[V] k') (EnrichedDayKernel.objects T F G k a)).hom ≫
        (EnrichedDayKernel.gen T F G k a ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry ((EnrichedDayKernel.Output.functor T F G).map k k') =
      EnrichedDayKernel.Output.actionGenerator T F G k k' a :=
  EnrichedDayKernel.Output.gen_naturality T F G k k' a

example (k : K) :
    eId V k ≫ (EnrichedDayKernel.Output.functor T F G).map k k =
      eId V (EnrichedDayKernel.obj T F G k) :=
  (EnrichedDayKernel.Output.functor T F G).map_id k

example (k k' k'' : K) :
    eComp V k k' k'' ≫ (EnrichedDayKernel.Output.functor T F G).map k k'' =
      ((EnrichedDayKernel.Output.functor T F G).map k k' ⊗ₘ
        (EnrichedDayKernel.Output.functor T F G).map k' k'') ≫
      eComp V (EnrichedDayKernel.obj T F G k) (EnrichedDayKernel.obj T F G k')
        (EnrichedDayKernel.obj T F G k'') :=
  (EnrichedDayKernel.Output.functor T F G).map_comp k k' k''

-- The constructor keeps the inverse braid rather than inserting a second positive crossing.
example (k k' : K) :
    MonoidalClosed.uncurry ((EnrichedDayKernel.Output.functor T F G).map k k') =
      (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F G k)).inv ≫
        MonoidalClosed.uncurry (EnrichedDayKernel.Output.actionDesc T F G k k') :=
  EnrichedDayKernel.Output.map_uncurry T F G k k'

end PlainRectangularIndices

section ActualTensorSpecialization

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I)
  (F G : EnrichedFunctor V I V)
  [∀ k : I, HasCoproduct (EnrichedDayKernel.relations d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoproduct (EnrichedDayKernel.objects d.tensorEnrichedFunctor F G k)]
  [∀ k : I, HasCoequalizer (EnrichedDayKernel.leftMap d.tensorEnrichedFunctor F G k)
    (EnrichedDayKernel.rightMap d.tensorEnrichedFunctor F G k)]

example : EnrichedFunctor V I V := EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G

example (k : I) :
    (EnrichedDayKernel.Output.functor d.tensorEnrichedFunctor F G).obj k =
      EnrichedDayKernel.obj d.tensorEnrichedFunctor F G k := rfl

end ActualTensorSpecialization

section ParticularKernelClients

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

section Identity
variable (k : K)
  [HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

-- Exactly one kernel exists here; a global per-k family is not supplied.
example : eId V k ≫ EnrichedDayKernel.Output.map T F G k k =
    eId V (EnrichedDayKernel.obj T F G k) :=
  EnrichedDayKernel.Output.map_id T F G k
end Identity

section Composition
variable (k k' k'' : K)
  [HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]
  [HasCoproduct (EnrichedDayKernel.relations T F G k')]
  [HasCoproduct (EnrichedDayKernel.objects T F G k')]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
    (EnrichedDayKernel.rightMap T F G k')]
  [HasCoproduct (EnrichedDayKernel.relations T F G k'')]
  [HasCoproduct (EnrichedDayKernel.objects T F G k'')]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k'')
    (EnrichedDayKernel.rightMap T F G k'')]

-- Exactly these three chosen kernels exist; unrelated output objects need no colimits.
example : eComp V k k' k'' ≫ EnrichedDayKernel.Output.map T F G k k'' =
    (EnrichedDayKernel.Output.map T F G k k' ⊗ₘ
      EnrichedDayKernel.Output.map T F G k' k'') ≫
      eComp V (EnrichedDayKernel.obj T F G k) (EnrichedDayKernel.obj T F G k')
        (EnrichedDayKernel.obj T F G k'') :=
  EnrichedDayKernel.Output.map_comp T F G k k' k''
end Composition

end ParticularKernelClients

#print axioms CategoryTheory.EnrichedDayKernel.Output.functor
#print axioms CategoryTheory.EnrichedDayKernel.Output.gen_naturality
#print axioms CategoryTheory.EnrichedDayKernel.Output.map_id
#print axioms CategoryTheory.EnrichedDayKernel.Output.map_comp
