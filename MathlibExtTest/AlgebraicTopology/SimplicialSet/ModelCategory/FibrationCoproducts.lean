/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationCoproducts

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

example {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) : Fibration (Limits.Sigma.map q) :=
  fibration_sigmaMap q hq

example {ι : Type u} {A B : ι → SSet.{u}} (q : ∀ c, A c ⟶ B c)
    (hq : ∀ c, Fibration (q c)) (k : Fin 2) :
    HasLiftingProperty (horn 1 k).ι (Limits.Sigma.map q) := by
  let _ : Fibration (Limits.Sigma.map q) := fibration_sigmaMap q hq
  exact (modelCategoryQuillen.fibration_iff (Limits.Sigma.map q)).mp inferInstance _ (horn_ι_mem_J 1 k)

end SSet
