/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeCofibrantComponents
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarTestPreservation

/-!
# Scalar preservation on the original native arrows

The original same-cardinal Q counit is level weak after scalar tensor when
the caller's components are cofibrant. Its full natural square compares
scalar tensor of the original arrow with scalar tensor of the original
Q arrow. The latter has all Omega-target tests by the original scalar
Quillen adjunction. Two-out-of-three transfers those tests to the former.

The complete source and target categories, stabilization family, original
Q functor, counit and all scalar maps are retained. Component cofibrancy
does not require the caller to be projectively cofibrant.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- Both original scalar Q-counit maps and their whole natural square
preserve and reflect every original Omega-target test of the scalar map. -/
theorem tensorQMap_omegaTests_iff_of_componentCofibrant
    (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hX : ∀ a : I, IsCofibrant (X.toEnrichedFunctor.obj a))
    (hY : ∀ a : I, IsCofibrant (Y.toEnrichedFunctor.obj a)) :
    omegaTests s ((EnrichedFunctorCat.tensorLeft M).map
        ((Replacement.cofibrantReplacement (B := B)).map f)) ↔
      omegaTests s ((EnrichedFunctorCat.tensorLeft M).map f) := by
  let W := omegaTests s
  have hqX : W ((EnrichedFunctorCat.tensorLeft M).map
      ((Replacement.cofibrantReplacementCounit (B := B)).app X)) :=
    levelWeak_le_omegaTests s _
      (NativeCofibrantComponents.scalar_originalQcounit_levelWeak_of_componentCofibrant
        hHom M X hX)
  have hqY : W ((EnrichedFunctorCat.tensorLeft M).map
      ((Replacement.cofibrantReplacementCounit (B := B)).app Y)) :=
    levelWeak_le_omegaTests s _
      (NativeCofibrantComponents.scalar_originalQcounit_levelWeak_of_componentCofibrant
        hHom M Y hY)
  have hn : (EnrichedFunctorCat.tensorLeft M).map
        ((Replacement.cofibrantReplacement (B := B)).map f) ≫
      (EnrichedFunctorCat.tensorLeft M).map
        ((Replacement.cofibrantReplacementCounit (B := B)).app Y) =
      (EnrichedFunctorCat.tensorLeft M).map
        ((Replacement.cofibrantReplacementCounit (B := B)).app X) ≫
      (EnrichedFunctorCat.tensorLeft M).map f := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      Replacement.cofibrantReplacementCounit_naturality]
  constructor
  · intro hf
    have h := W.comp_mem _ _ hf hqY
    rw [hn] at h
    exact W.of_precomp _ _ hqX h
  · intro hf
    have h := W.comp_mem _ _ hqX hf
    rw [← hn] at h
    exact W.of_postcomp _ _ hqY h

/-- Every original map with cofibrant components retains all Omega tests
after tensoring with an arbitrary cofibrant scalar. The source-Hom proof
supplies actual Q-component cofibrancy for the original replacement. -/
theorem tensorMap_omegaTests_of_componentCofibrant
    (s : NativeStabilizationFamily.{u, v} I L)
    (hHom : ∀ a b : I, IsCofibrant (a ⟶[PointedCGWH.{u, v}] b))
    (M : PointedCGWH.{u, v}) [IsCofibrant M]
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I} (f : X ⟶ Y)
    (hX : ∀ a : I, IsCofibrant (X.toEnrichedFunctor.obj a))
    (hY : ∀ a : I, IsCofibrant (Y.toEnrichedFunctor.obj a))
    (hf : omegaTests s f) :
    omegaTests s ((EnrichedFunctorCat.tensorLeft M).map f) :=
  (tensorQMap_omegaTests_iff_of_componentCofibrant s hHom M f hX hY).mp
    (tensorQMap_omegaTests s M f hf)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
