/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSmashModel
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor

/-!
# Scalar tensor on native maps with cofibrant components

The original pointwise weak class and the actual tensor Quillen adjunction
prove preservation for all source indices and cofibrant coefficients.
Component cofibrancy supplies the Brown argument at every original object.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeScalarComponentWeakPreservation

attribute [local instance] Native.modelCategory
  CGWH.modelCategory.instPointedCGWHIsClosedSymmetricMonoidalModelCategory

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- Every original weak native map with cofibrant components is preserved by
scalar tensor at an arbitrary cofibrant pointed coefficient. -/
theorem tensorMap_levelWeak_of_componentCofibrant
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hX : ∀ a : I, IsCofibrant (X.toEnrichedFunctor.obj a))
    (hY : ∀ a : I, IsCofibrant (Y.toEnrichedFunctor.obj a))
    (hf : weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I) f) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((EnrichedFunctorCat.tensorLeft M).map f) := by
  rw [Native.weakEquivalences_eq, EvaluationTransfer.evaluationProperty_iff] at hf ⊢
  intro a
  let _ : IsCofibrant (X.toEnrichedFunctor.obj a) := hX a
  let _ : IsCofibrant (Y.toEnrichedFunctor.obj a) := hY a
  let _ : (ihom.adjunction M).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant M
  let _ : WeakEquivalence (component f a) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hf a)
  change weakEquivalences PointedCGWH.{u, v} (component (tensorLeftMap M f) a)
  rw [tensorLeftMap_component]
  change weakEquivalences PointedCGWH.{u, v}
    ((MonoidalCategory.tensorLeft M).map (component f a))
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ihom.adjunction M) (component f a))

end HomotopicalAlgebra.EnrichedProjective.Native.NativeScalarComponentWeakPreservation
