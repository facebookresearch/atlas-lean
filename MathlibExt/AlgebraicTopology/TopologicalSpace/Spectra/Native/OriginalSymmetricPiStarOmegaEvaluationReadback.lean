/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalSymmetricPiStarOmegaDetection

/-!
# The original first free comparison in the native coordinate

The same original one-step evaluation comparison and coaugmentation give the
complete first free-function word at every native input and natural degree.
The original scalar, index and carrier maps are retained.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat NativeOmegaRecovery
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport.Sequential

namespace PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  MonoidalClosed.enrichedOrdinaryCategorySelf PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  Operad.SmallFinBijGroupoid.instMonoidalCategory Operad.SmallFinBijGroupoid.instSymmetricCategory

/-- The chosen native successor evaluation retains its original entire comparison component. -/
private theorem native_levelComparison_hom_app (m : ℕ) (X : Carrier.{u, v}) :
    (NativeSymmetricR.levelComparison.{u, v} m).hom.app X =
      (NativeSymmetricR.level.{u, v} m).map (NativeSymmetricR.comparison.{u, v}.hom.app X) := by
  simp only [NativeSymmetricR.levelComparison, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  exact Category.comp_id _

private theorem actualLevel_eq_nativeLevel (m : ℕ) :
    level.{u, v} m = NativeSymmetricR.level.{u, v} m := rfl

private theorem equal_functors_map_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual evaluation chart retains the whole original first free comparison. -/
theorem original_stepEvaluation_hom_app (m : ℕ) (X : Carrier.{u, v}) :
    (stepEvaluation.{u, v} m).hom.app X =
      (level.{u, v} m).map (NativeSymmetricR.comparison.{u, v}.hom.app X) := by
  have h := native_levelComparison_hom_app.{u, v} m X
  have hMap := equal_functors_map_heq (actualLevel_eq_nativeLevel.{u, v} m)
    (NativeSymmetricR.comparison.{u, v}.hom.app X)
  exact h.trans (eq_of_heq hMap).symm

end PointedCGWH.Spectra.OriginalSymmetricPiStarOmegaTests
