/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Kernel

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
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K)

example (a : C × D) :
    EnrichedDayKernel.objects T F G k a =
      (T.obj a ⟶[V] k) ⊗ (F.obj a.1 ⊗ G.obj a.2) := rfl

variable [HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

-- No category on C, D or K and no colimits for an unrelated diagram are supplied.
example : EnrichedDayKernel.desc T F G k
    (EnrichedDayKernel.gen T F G k) (EnrichedDayKernel.gen_balanced T F G k) =
      𝟙 (EnrichedDayKernel.obj T F G k) := by
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  rw [EnrichedDayKernel.gen_desc, Category.comp_id]

example (X : V) :
    (EnrichedDayKernel.obj T F G k ⟶ X) ≃
      {q : ∀ a, EnrichedDayKernel.objects T F G k a ⟶ X //
        EnrichedDayKernel.Balanced T F G k q} :=
  EnrichedDayKernel.homEquiv T F G k X

end PlainRectangularIndices

section ActualEnrichedTensor

attribute [local instance] CategoryTheory.Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (k : I)

example (i j : I) :
    (EnrichedDayKernel.weight d.tensorEnrichedFunctor k).obj (Opposite.op (i, j)) =
      ((i ⊗ j) ⟶[V] k) := rfl

example (a b : I × I) :
    MonoidalClosed.uncurry
        ((EnrichedDayKernel.weight d.tensorEnrichedFunctor k).map
          (Opposite.op b) (Opposite.op a)) =
      ((b.1 ⊗ b.2) ⟶[V] k) ◁ d.tensorMap a.1 b.1 a.2 b.2 ≫
        (β_ ((b.1 ⊗ b.2) ⟶[V] k) ((a.1 ⊗ a.2) ⟶[V] (b.1 ⊗ b.2))).hom ≫
        eComp V (a.1 ⊗ a.2) (b.1 ⊗ b.2) k :=
  EnrichedDayKernel.weight_uncurry_map d.tensorEnrichedFunctor k a b

end ActualEnrichedTensor

#print axioms CategoryTheory.EnrichedDayKernel.oppositeTensor
#print axioms CategoryTheory.EnrichedDayKernel.gen_desc
#print axioms CategoryTheory.EnrichedDayKernel.homEquiv
