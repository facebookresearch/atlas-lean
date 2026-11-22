/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.NativePairCoefficient
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.EvaluationLabelCast
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Evaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.EvaluationReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion

/-!
# Native Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.UnitLiftFamily
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion.SourceJoin
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback

/-- The exact original native tensor unit is retained as one typed object. -/
def nativeUnitObject : CanonicalSourceSmash.Carrier.{u, v} :=
  letI := CanonicalSourceSmash.monoidalCategory.{u, v}
  𝟙_ CanonicalSourceSmash.Carrier.{u, v}

/-- The unit object getter keeps the actual canonical tensor-unit value. -/
theorem nativeUnitObject_original :
    nativeUnitObject.{u, v} =
      (letI := CanonicalSourceSmash.monoidalCategory.{u, v}
       𝟙_ CanonicalSourceSmash.Carrier.{u, v}) := rfl

/-- The existing native lift is exactly the original pair-inverse and right-unitor recipe. -/
theorem nativeUnitLift_eq_rightLift (n r : ℕ) (K : PointedCGWH.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶
      nativeUnitObject.{u, v}) :
    nativeUnitLift.{u, v} n r K g =
      rightLift (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
        CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
        (fun n r => n + r) nativePairFamily.{u, v} n r
        (PointedCGWH.orthogonalSphere.{u, v} n) K g := by
  delta nativeUnitLift nativeUnitObject
  exact liftFamily_eq_rightLift (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v} n r K g

/-- The target map is the same native lift evaluated on the original free/evaluation counit. -/
def nativeUnitLiftTarget (n r : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ⊗
      nativeUnitObject.{u, v}.toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} r) ⟶
      (sphereFree.{u, v} n).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)) :=
  liftFamilyTarget (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v} n r

/-- The typed target has exactly the unchanged native lift on the original free/evaluation counit. -/
theorem nativeUnitLiftTarget_original (n r : ℕ) :
    nativeUnitLiftTarget.{u, v} n r =
      Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
    (PointedCGWH.orthogonalSphere.{u, v} n ⊗
      nativeUnitObject.{u, v}.toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} r))
    (sphereFree.{u, v} n)
    (nativeUnitLift.{u, v} n r
      (nativeUnitObject.{u, v}.toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} r))
      (Free.extend (OrthogonalOperatorIndex.ofIndex.{u, v} r)
        (nativeUnitObject.{u, v}.toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex.{u, v} r))
        nativeUnitObject.{u, v} (𝟙 _))) := by
  delta nativeUnitLiftTarget nativeUnitLift nativeUnitObject
  exact liftFamilyTarget_original (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v} n r

/-- Every arbitrary native unit map factors through its original counit evaluation. -/
theorem nativeUnitLift_evaluate (n r : ℕ) (K : PointedCGWH.{u, v})
    (g : Free.object (OrthogonalOperatorIndex.ofIndex.{u, v} r) K ⟶
      nativeUnitObject.{u, v}) :
    Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))
      (PointedCGWH.orthogonalSphere.{u, v} n ⊗ K) (sphereFree.{u, v} n)
      (nativeUnitLift.{u, v} n r K g) =
        (PointedCGWH.orthogonalSphere.{u, v} n ◁
          Free.evaluate (OrthogonalOperatorIndex.ofIndex.{u, v} r) K
            nativeUnitObject.{u, v} g) ≫ nativeUnitLiftTarget.{u, v} n r := by
  delta nativeUnitLiftTarget nativeUnitLift nativeUnitObject
  exact liftFamily_evaluate (V := PointedCGWH.{u, v}) (J := OrthogonalOperatorIndex.{u, v})
    CanonicalSourceSmash.monoidalCategory.{u, v} OrthogonalOperatorIndex.ofIndex.{u, v}
    PointedCGWH.orthogonalSphere.{u, v} nativePairFamily.{u, v} nativePair_coefficient_family.{u, v}
    n r K g

/-- The target factor retains the original r+n/n+r target equality without altering any action. -/
def nativeUnitLiftOriginalTarget (n r : ℕ) :
    PointedCGWH.orthogonalSphere.{u, v} n ⊗
      nativeUnitObject.{u, v}.toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} r) ⟶
      (sphereFree.{u, v} n).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (r + n)) :=
  nativeUnitLiftTarget.{u, v} n r ≫
    eqToHom (congrArg (fun j => (sphereFree.{u, v} n).toEnrichedFunctor.obj
      (OrthogonalOperatorIndex.ofIndex.{u, v} j)) (Nat.add_comm r n).symm)

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
