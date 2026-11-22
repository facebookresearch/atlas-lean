/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHom

/-!
# The same original pointed coherent Hom functor

The actual endpoint readbacks retain identities and both full source
maps under composition. They make the entire original coherent Hom
assignment a functor on the original pointed source category.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The same original pointed coherent Hom identity is the whole original identity map. -/
theorem homMap_id (X : Category.{u}) : homMap (𝟙 X) = 𝟙 (homObject X) := by
  dsimp only [homMap, pointedHomMap]
  have h := EnrichedFunctor.homMap_eq (realizationMap_id X.right)
    (sourceVertex_map (𝟙 X)) (targetVertex_map (𝟙 X)) rfl rfl
  exact h.trans (EnrichedFunctor.homMap_id (C := realization X.right) (sourceVertex X) (targetVertex X))

/-- Both same original pointed source Hom maps compose to their exact original source composition. -/
theorem homMap_comp {X Y Z : Category.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMap f ≫ homMap g = homMap (f ≫ g) :=
  pointedHomMap_comp f.right g.right (sourceVertex_map f) (targetVertex_map f)
    (sourceVertex_map g) (targetVertex_map g)

/-- The entire same original pointed coherent endpoint Hom functor. -/
def homFunctor : Category.{u} ⥤ SSet.{u} where
  obj := homObject
  map := homMap
  map_id := homMap_id
  map_comp f g := (homMap_comp f g).symm

end CategoryTheory.CoherentRealization.OriginalPointed
