/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOneSphereRecognition
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableClassAssembly
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationKAdapter
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorHomCofibrant
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ThomCofibrant
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.CanonicalLevelModel
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK
import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor

/-!
# Original generator-class inputs on the three native spectrum carriers

The sequential, symmetric and orthogonal branches use their actual
stabilization families. Their one-sphere labels cover every original index
object, and the actual coefficient isomorphisms identify the coefficients
with the native pointed one-sphere. The symmetric label retains its source
finite set and its added singleton; the orthogonal label retains its
source dimension and added one-dimensional representation.

The original sphere, orbit-copower and Thom cell arguments prove the
index-Hom cofibrancy needed for all-source K-left acyclicity. Each branch
therefore supplies the full original K-left test class and the chosen-fiber
criterion on its original continuous enriched carrier.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open CategoryTheory.MonoidalCategory.TensorPower
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeStable

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The original natural degree selects its literal sequential one-step label. -/
def sequentialOneStep (a : PointedCGWH.Spectra.Sequential.Index.{u, v}) : ℕ := a.degree

/-- Every original sequential index object is the unchanged source of its selected label. -/
theorem sequentialOneStep_source (a : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    SequentialSpectrum.StabilizationKAdapter.family.source (sequentialOneStep a) = a := by
  cases a
  rfl

/-- The original sequential coefficient is literally the native one-sphere. -/
def sequentialOneStepCoefficientIso (a : PointedCGWH.Spectra.Sequential.Index.{u, v}) :
    SequentialSpectrum.StabilizationKAdapter.family.coefficient (sequentialOneStep a) ≅
      PointedCGWH.sphereOne.{u, v} := Iso.refl _

/-- The original finite-bijection object and added singleton select an actual full-family label. -/
def symmetricOneStep (a : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    CategoryTheory.Operad.SmallFinBijGroupoid × CategoryTheory.Operad.SmallFinBijGroupoid := by
  rcases a with ⟨a⟩
  exact (a, CategoryTheory.Operad.SmallFinBijGroupoid.card 1)

/-- Every original symmetric operator object is retained by that full paired label. -/
theorem symmetricOneStep_source (a : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    Actual.symmetricFamily.source (symmetricOneStep a) = a := by
  cases a
  rfl

/-- The singleton sphere coefficient uses the original tensor-power unitor. -/
def symmetricOneStepCoefficientIso (a : PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    Actual.symmetricFamily.coefficient (symmetricOneStep a) ≅
      PointedCGWH.sphereOne.{u, v} := tensorPowObjOneIso _

/-- The original dimension and added line select an actual orthogonal full-family label. -/
def orthogonalOneStep (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) : ℕ × ℕ := by
  rcases a with ⟨a⟩
  exact (a, 1)

/-- Every original orthogonal operator object remains the source of that paired label. -/
theorem orthogonalOneStep_source (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    Actual.orthogonalFamily.source (orthogonalOneStep a) = a := by
  cases a
  rfl

/-- The actual line compactification uses its original pointed boundary-quotient comparison. -/
def orthogonalOneStepCoefficientIso
    (a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    Actual.orthogonalFamily.coefficient (orthogonalOneStep a) ≅
      PointedCGWH.sphereOne.{u, v} :=
  CategoryTheory.Spectra.orthogonalOneSphereIsoSphereOne

/-- The original Thom cell proof covers every full continuous orthogonal operator Hom. -/
theorem orthogonalHom_isCofibrant
    (a b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :
    IsCofibrant (a ⟶[PointedCGWH.{u, v}] b) := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  exact CategoryTheory.Spectra.OrthogonalCoendThom.nativeHom_isCofibrant a b

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- All original sequential K-left arrows satisfy every original Omega-target test. -/
theorem sequentialKLeft_le_omegaTests :
    (NativeK.generators SequentialSpectrum.StabilizationKAdapter.family.{u, v}).rlp.llp ≤
      NativeK.omegaTests SequentialSpectrum.StabilizationKAdapter.family :=
  NativeK.originalKLeft_le_localTests SequentialSpectrum.StabilizationKAdapter.family
    PointedCGWH.Spectra.Sequential.hom_isCofibrant

/-- The entire paired symmetric K-left class is acyclic on arbitrary original endpoints. -/
theorem symmetricKLeft_le_omegaTests :
    (NativeK.generators Actual.symmetricFamily.{u, v}).rlp.llp ≤
      NativeK.omegaTests Actual.symmetricFamily :=
  NativeK.originalKLeft_le_localTests Actual.symmetricFamily
    PointedCGWH.SymmetricOperatorHom.nativeSymmetricOperatorHom_isCofibrant

/-- The entire paired orthogonal K-left class is acyclic on the original continuous carrier. -/
theorem orthogonalKLeft_le_omegaTests :
    (NativeK.generators Actual.orthogonalFamily.{u, v}).rlp.llp ≤
      NativeK.omegaTests Actual.orthogonalFamily :=
  NativeK.originalKLeft_le_localTests Actual.orthogonalFamily orthogonalHom_isCofibrant

/-- The full symmetric K-right test-null fiber gives every original finite-index component. -/
theorem symmetric_chosenFiber_levelTrivialFibration
    {X Y : Actual.SymmetricCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (NativeK.generators Actual.symmetricFamily).rlp p)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hTests : NativeK.omegaTests Actual.symmetricFamily c.snd) :
    trivialFibrations Actual.SymmetricCarrier.{u, v} p ∧
      ∀ a : PointedCGWH.SymmetricOperatorIndex.{u, v},
        trivialFibrations PointedCGWH.{u, v} (component p a) :=
  NativeK.chosenFiber_omegaTests_levelTrivialFibration Actual.symmetricFamily
    symmetricOneStep symmetricOneStep_source symmetricOneStepCoefficientIso p hp c hc hTests

/-- The full orthogonal K-right test-null fiber gives every original dimensional component. -/
theorem orthogonal_chosenFiber_levelTrivialFibration
    {X Y : Actual.OrthogonalCarrier.{u, v}} (p : X ⟶ Y)
    (hp : (NativeK.generators Actual.orthogonalFamily).rlp p)
    (c : PullbackCone p (zeroTo Y)) (hc : IsLimit c)
    (hTests : NativeK.omegaTests Actual.orthogonalFamily c.snd) :
    trivialFibrations Actual.OrthogonalCarrier.{u, v} p ∧
      ∀ a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v},
        trivialFibrations PointedCGWH.{u, v} (component p a) :=
  NativeK.chosenFiber_omegaTests_levelTrivialFibration Actual.orthogonalFamily
    orthogonalOneStep orthogonalOneStep_source orthogonalOneStepCoefficientIso p hp c hc hTests

end PointedCGWH.Spectra.NativeStable
