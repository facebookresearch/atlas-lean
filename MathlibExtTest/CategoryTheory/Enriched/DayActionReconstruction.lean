/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ActionReconstruction

set_option autoImplicit false
noncomputable section
universe uV vV uC uD uK
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace DayActionReconstructionClient
open Limits EnrichedDayKernel
attribute [local instance] Enriched.prodCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]
  {K : Type uK} [EnrichedCategory V K]
  (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
  (X : EnrichedFunctor V K V)
  [∀ k : K, HasCoproduct (relations T F G k)]
  [∀ k : K, HasCoproduct (objects T F G k)]
  [∀ k : K, HasCoequalizer (leftMap T F G k) (rightMap T F G k)]
  (m : (⟨Output.functor T F G⟩ : EnrichedFunctorCat V K) ⟶ ⟨X⟩)

/-- Extraction retains the entire product enriched Hom action. -/
theorem full_product_hom (a b : C × D) :
    MonoidalClosed.uncurry ((F.externalTensor G).map a b) ≫
      ActionFromTransformation.component T F G X
        (ActionFromTransformation.extract T F G X m) b =
    (ActionFromTransformation.component T F G X
        (ActionFromTransformation.extract T F G X m) a ⊗ₘ 𝟙 (a ⟶[V] b)) ≫
      MonoidalClosed.uncurry ((T.comp V X).map a b) :=
  (ActionFromTransformation.extract T F G X m).uncurriedNaturality a b

/-- Every full coend generator, with no choice of a Hom label, recovers the action. -/
theorem every_generator (k : K) (a : C × D) :
    gen T F G k a ≫ EnrichedFunctorCat.component m k =
      ActionFromTransformation.generator T F G X
        (ActionFromTransformation.extract T F G X m) k a :=
  (ActionFromTransformation.gen_extract T F G X m k a).symm

/-- Recovery is an equality of genuine transformations on the complete output. -/
theorem whole_action :
    ActionFromTransformation.transformation T F G X
      (ActionFromTransformation.extract T F G X m) = m :=
  ActionFromTransformation.transformation_extract T F G X m

end DayActionReconstructionClient
