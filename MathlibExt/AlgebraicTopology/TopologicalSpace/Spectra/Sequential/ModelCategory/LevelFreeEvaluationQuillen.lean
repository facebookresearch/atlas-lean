/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.OrdinaryLevelModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# Free evaluation for the ordinary sequential level model

For each natural-number level, free generation and evaluation form a Quillen
adjunction on pointed compactly generated weak Hausdorff sequential spectra.
The theorem uses the specified ordinary native level model and the adjunction
for the sphere-one suspension coordinate.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum

/-- Actual native free generation and literal evaluation form a Quillen
adjunction for the chosen ordinary native level model. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : ℕ) :
    let _ : ModelCategory PointedCGWH.SequentialSpectrum.{u, v} :=
      PointedCGWH.Spectra.Sequential.levelModel
    (freeAtEvaluationAdjunction PointedCGWH.sphereOne.{u, v} n).IsQuillenAdjunction := by
  change (letI : ModelCategory PointedCGWH.Spectra.Sequential.Spectrum.{u, v} :=
    PointedCGWH.Spectra.Sequential.levelModel
    (CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction
      PointedCGWH.sphereOne.{u, v} n).IsQuillenAdjunction)
  exact PointedCGWH.Spectra.Sequential.freeAtEvaluation_isQuillenAdjunction n

end PointedCGWH.SequentialSpectrum
