/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.MappingCylinderBasedHEP
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeIndexKanHomotopyExtension
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.HomotopyExtensionClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.RightShift

/-!
# Based homotopy extension after scalar Kan extension

For a realized boundary inclusion of pointed spaces, scalar tensoring with
an arbitrary native orthogonal spectrum gives based homotopy extension.
Left Kan extension along a right index shift preserves that property,
giving `scalarKan_boundary` at every orthogonal index.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open scoped CGWH.modelCategory

namespace OrthogonalIGeneratorProbe.FinalHEPCompatible

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.EnrichedKan.hasObjectCoproduct PointedCGWH.EnrichedKan.hasRelationCoproduct
  PointedCGWH.EnrichedKan.hasBalancingCoequalizer

/-- Every original coefficient boundary has HEP after scalar tensor and index Kan extension, for arbitrary
native spectra. -/
theorem scalarKan_boundary (r : OrthogonalIndex) {K L : PointedCGWH.{u, v}}
    (i : K ⟶ L) (hi : PointedCGWH.realizedBoundaryInclusions i)
    (Y : FunctionSpectrum.RightShift.Carrier.{u, v}) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((leftKan (FunctionSpectrum.RightShift.indexShift.{u, v} r)).map
        (scalarTensorMap i Y)) :=
  HomotopicalAlgebra.EnrichedProjective.Native.NativeIndexKanHomotopyExtension.leftKan_map_HEP
    (FunctionSpectrum.RightShift.indexShift.{u, v} r) (scalarTensorMap i Y)
    (PointedCGWH.EnrichedBasedHomotopyExtension.scalarTensorMap_mem i
      (PointedCGWH.BasedTimeHomotopyExtension.modelCofibration_mem i
        (OriginalIClosedHomotopyExtension.boundaryMap_modelCofibration i hi)) Y)



end OrthogonalIGeneratorProbe.FinalHEPCompatible
