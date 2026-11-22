/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.ModelCategory.LevelModel

/-!
# The ordinary native sequential projective level model

The original ordinary class readbacks refer to
`PointedCGWH.Spectra.Sequential.levelModel`. The native generator labels
characterize the classes of that same canonical value.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum

/-- The canonical value retains the literal boundary left class. -/
theorem ordinaryLevelModelCategory_cofibrations :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithCofibrations.cofibrations =
      boundaryGenerators.{u, v}.rlp.llp := by
  exact levelModelCategory_cofibrations

/-- Its actual fibration class is exactly the class detected by each level. -/
theorem ordinaryLevelModelCategory_fibrations_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithFibrations.fibrations f ↔
      ∀ n : ℕ, fibrations PointedCGWH.{u, v} (levelMap f n) := by
  exact levelModelCategory_fibrations_iff f

/-- Its actual weak-equivalence class is exactly levelwise weak equivalence. -/
theorem ordinaryLevelModelCategory_weakEquivalences_iff
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences f ↔
      ∀ n : ℕ, weakEquivalences PointedCGWH.{u, v} (levelMap f n) := by
  exact levelModelCategory_weakEquivalences_iff f

/-- Its actual trivial-fibration class is the literal boundary right class. -/
theorem ordinaryLevelModelCategory_trivialFibrations :
    (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithFibrations.fibrations ⊓
      (PointedCGWH.Spectra.Sequential.levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences =
        boundaryGenerators.{u, v}.rlp := by
  exact levelModelCategory_trivialFibrations

end PointedCGWH.SequentialSpectrum
