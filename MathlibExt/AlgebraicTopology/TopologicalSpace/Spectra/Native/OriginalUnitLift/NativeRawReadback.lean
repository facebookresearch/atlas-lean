/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativeShiftedFamily

/-!
# Native Raw Readback

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback

/-- Evaluate the unchanged original source-label cast and native counit lift at the original r+n target. -/
def nativeRawLiftTarget (n r : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ⊗
      nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r) ⟶
        (sphereFree.{u, v} n).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n)) :=
  freeMapFamilyTarget (OrthogonalOperatorIndex.ofIndex.{u, v} r)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
    (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
    (nativeShiftedLiftFamily.{u, v} n r)

/-- The target factor retains the literal source label cast, native lift and entire free/evaluation counit. -/
theorem nativeRawLiftTarget_original (n r : ℕ) :
    nativeRawLiftTarget.{u, v} n r =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
        (PointedCGWH.orthogonalSphere.{u, v} n ⊗
          nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))
        (sphereFree.{u, v} n)
        (nativeFreeLabelCast (Nat.add_comm r n)
            (PointedCGWH.orthogonalSphere.{u, v} n ⊗
              nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r)) ≫
          nativeUnitLift.{u, v} n r
            (nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))
            (Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} r)
              (nativeUnitObject.{u, v}.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} r))
              nativeUnitObject.{u, v} (𝟙 _))) := rfl

/-- The literal original raw mixed evaluator of every native lift factors through the original unit evaluation. -/
theorem nativeUnitLift_rawMixedEvaluate (n r d : ℕ)
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r)
      (PointedCGWH.orthogonalSphere.{u, v} d) ⟶ nativeUnitObject.{u, v}) :
    rawMixedEvaluate (sphereFree.{u, v} n) r d n
      (nativeUnitLift.{u, v} n r (PointedCGWH.orthogonalSphere.{u, v} d) g) =
      (PointedCGWH.orthogonalSphere.{u, v} n ◁
        Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r)
          (PointedCGWH.orthogonalSphere.{u, v} d) nativeUnitObject.{u, v} g) ≫
            nativeRawLiftTarget.{u, v} n r :=
  freeMapFamily_evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r)
    (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n))
    (PointedCGWH.orthogonalSphere.{u, v} n) nativeUnitObject.{u, v} (sphereFree.{u, v} n)
    (nativeShiftedLiftFamily.{u, v} n r) (nativeShiftedLiftFamily_naturality.{u, v} n r)
    (PointedCGWH.orthogonalSphere.{u, v} d) g

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
