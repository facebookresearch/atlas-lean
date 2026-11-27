/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP

/-!
# Reflection of boundary lifting by the singular functor

A topological map has the right lifting property against all realized simplicial
boundary inclusions exactly when its singular image has the right lifting property
against all simplicial boundary inclusions. The reverse implication transports each
realized boundary square back through the realization–singular adjunction.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/--
If the singular image of a topological map lifts against every simplicial boundary,
the map lifts against each realized boundary inclusion.
-/
theorem toSSet_I_rlp_mem_boundaryRLP {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet f)
    {A B : TopCat.{u}} {g : A ⟶ B} (hg : realizedBoundaryInclusions g) :
    HasLiftingProperty g f := by
  obtain ⟨n⟩ := hg
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.boundary n).ι f).mpr
    (hf _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n))

/--
The singular inverse image of the simplicial boundary right lifting class is
contained in the realized-boundary right lifting class.
-/
theorem inverseImage_I_rlp_le_boundaryRLP :
    (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet ≤
      realizedBoundaryInclusions.rlp := by
  intro X Y f hf A B g hg
  exact toSSet_I_rlp_mem_boundaryRLP hf hg

/--
The realized-boundary right lifting class equals the singular inverse image of
the simplicial boundary right lifting class.
-/
theorem boundaryRLP_eq_inverseImage_I_rlp :
    realizedBoundaryInclusions.rlp =
      (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet :=
  le_antisymm boundaryRLP_le_inverseImage_I_rlp
    inverseImage_I_rlp_le_boundaryRLP

end TopCat
