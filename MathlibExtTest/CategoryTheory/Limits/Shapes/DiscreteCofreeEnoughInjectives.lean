/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import MathlibExt.CategoryTheory.Limits.Shapes.DiscreteCofreeEnoughInjectives

/-!
# Injective presentations of diagrams

For independent index and value categories, these clients use pullbacks,
sized products and enough injectives to obtain diagram presentations. They
check that each component of the presentation is monic and that a map into
its injective target extends through any monomorphism of diagrams.
-/

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace DiscreteCofreeEnoughInjectivesTests

variable {I : Type u₁} [Category.{v₁} I]
  {C : Type u₂} [Category.{v₂} C]
  [HasPullbacks C] [HasProducts.{max u₁ v₁} C] [EnoughInjectives C]

local instance : EnoughInjectives (I ⥤ C) := enoughInjectives_functorCategory_of_products

/-- The actual injective presentation is mono at each index, with universes independent. -/
example (M : I ⥤ C) (i : I) : Mono ((Injective.ι M).app i) := by
  change Mono (((evaluation I C).obj i).map (Injective.ι M))
  infer_instance

/-- An actual map into that injective envelope extends through any actual mono. -/
example (K : I ⥤ C) {M N : I ⥤ C} (f : M ⟶ N) [Mono f]
    (g : M ⟶ Injective.under K) : f ≫ Injective.factorThru g f = g :=
  Injective.comp_factorThru g f

end DiscreteCofreeEnoughInjectivesTests

end
