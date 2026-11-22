/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyCofibrant

/-!
# Reedy weak equivalences in the all-CSS Rezk weak class
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
namespace SimplicialSpace

theorem reedyWeak_le_rezkWeak :
    let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    weakEquivalences SimplicialSpace.{u} ≤ rezkWeakEquivalences.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  change weakEquivalences SimplicialSpace.{u} ≤ rezkWeakEquivalences.{u}
  intro X Y f hf Z hZ
  have hX : IsCofibrant X := ReedyModel.isCofibrant X
  have hY : IsCofibrant Y := ReedyModel.isCofibrant Y
  have hZf : IsFibrant Z := hZ.1
  exact ReedyModel.inner_precomp_weak_of_weak f Z hX hY hf hZf

end SimplicialSpace
