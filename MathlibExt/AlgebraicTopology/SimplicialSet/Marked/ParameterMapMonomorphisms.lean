/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms

/-!
# Original monic parameter maps remain monic in every marked slice

The original parameter map acts by its original first-coordinate function
and the identity on the whole marked source. Native component injectivity
therefore proves monicity without any marked-model, base-fibrancy or
source-size premise.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked

/-- The original maximal parameter product preserves native parameter monomorphisms. -/
theorem maxTensor_map_mono (X : Marked.{u}) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    Mono ((maxTensorFunctor X).map a) := by
  let f : prod (max A) X ⟶ prod (max D) X := prodMap (maximal.map a) (𝟙 X)
  let _ : ∀ n : SimplexCategoryᵒᵖ, Mono (f.hom.app n) := fun n =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro x y h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      apply Prod.ext
      · exact (injective_of_mono (a.app n)) h₁
      · exact h₂)
  let _ : Mono f.hom := NatTrans.mono_of_mono_app _
  exact Hom.mono_of_underlying f

/-- The same whole original monic parameter map is monic over any supplied marked base. -/
theorem overParameter_map_mono (Z : Marked.{u}) (X : Over Z) {A D : SSet.{u}}
    (a : A ⟶ D) [Mono a] : Mono ((overParameterFunctor Z X).map a) := by
  let _ : Mono ((overParameterFunctor Z X).map a).left := maxTensor_map_mono X.left a
  exact Over.mono_of_mono_left _

end SSet.Marked
