/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.MappingCornerFactorWeak
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IntervalModel
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK

/-!
# All-label native stabilization corner weakness from original K lifting

The original K factory supplies the original source cylinder, its
original weak contraction, both actual cofibrant free endpoints, and
the entire first-factor trivial-fibration corner. Original source Brown
and scalar right properness transfer weakness to the entire original
stabilization corner. The given target arrow is arbitrary.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedFunctorMapping
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B₀ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (s : NativeStabilizationFamily.{u, v} I L)

/-- Every original K-right map has a weak whole stabilization corner
at every original label and every original chosen strict corner. -/
theorem stabilizationCorner_weak_of_right
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (hp : (generators s).rlp p) (l : L)
    (corner : WeightedEndVariance.bifunctor.PullbackObjObj (stabilization s l) p) :
    weakEquivalences PointedCGWH.{u, v} corner.π := by
  let _ : IsRightProper PointedCGWH.{u, v} :=
    isRightProper_of_all_objects_fibrant PointedCGWH.modelCategory.allObjectsFibrant
  let _ : IsCofibrant (Arrow.mk (stabilization s l)).left :=
    stabilization_source_cofibrant s l
  let _ : (tensorMappingAdjunction (Arrow.mk (stabilization s l)).left).IsQuillenAdjunction :=
    PointedCGWH.EnrichedIntervalCylinderModel.coefficient_isQuillen _
  have h := (lifting_iff s p).mp hp
  have hpost : fibrations PointedCGWH.{u, v}
      ((WeightedEndVariance.bifunctor.obj
        (Opposite.op (Arrow.mk (stabilization s l)).left)).map p) :=
    Adjunction.IsQuillenAdjunction.preservesFibrations
      (adj := tensorMappingAdjunction (Arrow.mk (stabilization s l)).left) p h.1
  have hX := cylinderRetraction_source_weak s l X
  have hY := cylinderRetraction_source_weak s l Y
  have hX' : weakEquivalences PointedCGWH.{u, v}
      ((WeightedEndVariance.bifunctor.map (cylinderRetraction s l).op).app X) := by
    simpa only [mapSource, PointedCGWH.NativeMappingSourceFunctor.source_eq,
      Functor.flip_obj_map] using hX
  have hY' : weakEquivalences PointedCGWH.{u, v}
      ((WeightedEndVariance.bifunctor.map (cylinderRetraction s l).op).app Y) := by
    simpa only [mapSource, PointedCGWH.NativeMappingSourceFunctor.source_eq,
      Functor.flip_obj_map] using hY
  exact MappingCornerFactorWeak.weak_of_factor WeightedEndVariance.bifunctor
    (cylinderSource s l) (cylinderRetraction s l) (stabilization s l) (cylinder_fac s l)
    p corner (PointedCGWH.NativeMappingCorner.square (cylinderSource s l) p)
    hX' hY' hpost (h.2 l).2

/-- The original canonical whole corner is a client of the theorem
that retains the caller's arbitrary chosen corner. -/
theorem stabilizationCorner_weak
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (p : X ⟶ Y) (hp : (generators s).rlp p) (l : L) :
    weakEquivalences PointedCGWH.{u, v}
      (PointedCGWH.NativeMappingCorner.square (stabilization s l) p).π :=
  stabilizationCorner_weak_of_right s p hp l
    (PointedCGWH.NativeMappingCorner.square (stabilization s l) p)

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
