/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory

/-!
# Cofibrancy of every simplicial space in the Rezk model

The named Reedy model gives a monic initial arrow. The same arrow is a
cofibration in the named Rezk model, whose cofibrations are monomorphisms.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SimplicialSpace.RezkModel

/-- Every simplicial space is cofibrant in the selected Rezk model. -/
theorem isCofibrant (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopicalAlgebra.IsCofibrant X := by
  have hm : Mono (initial.to X) := by
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    exact (ReedyModel.cofibration_iff (initial.to X)).1
      ((HomotopicalAlgebra.isCofibrant_iff X).1 (ReedyModel.isCofibrant X))
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.isCofibrant_iff, HomotopicalAlgebra.cofibration_iff]
  change modelCategory.categoryWithCofibrations.cofibrations (initial.to X)
  rw [modelCategory_cofibrations]
  exact hm

end SimplicialSpace.RezkModel
