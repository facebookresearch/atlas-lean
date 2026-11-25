/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP

/-!
# Boundary-RLP reflection across the realization/singular adjunction

This file is part of the KQ3 layer. It is the converse of the staged
`BoundaryRLPSingularRLP` transport: a `TopCat` map whose singular image lifts
against all simplicial boundary inclusions already lifts against all realized
boundary inclusions. Each realized generator is a realized simplicial boundary,
so `sSetTopAdj.hasLiftingProperty_iff` moves the problem back to `SSet`, where
`SSet.modelCategoryQuillen.boundary_ι_mem_I` applies. Combined with the staged
forward inclusion, the two `rlp` properties agree.

This proves only the formal KQ3 adjunction reflection isolated by `v0973`. It
assumes no external `J.rlp` theorem, no model structure, and no target
trivial-fibration inclusion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Morphism-level reflection: singular boundary-RLP maps lift against every
realized boundary generator. -/
theorem toSSet_I_rlp_mem_boundaryRLP {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet f)
    {A B : TopCat.{u}} {g : A ⟶ B} (hg : realizedBoundaryInclusions g) :
    HasLiftingProperty g f := by
  obtain ⟨n⟩ := hg
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.boundary n).ι f).mpr
    (hf _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n))

/-- Property-level reflection: the singular inverse image of `I.rlp` lies in
realized boundary-RLP maps. -/
theorem inverseImage_I_rlp_le_boundaryRLP :
    (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet ≤
      realizedBoundaryInclusions.rlp := by
  intro X Y f hf A B g hg
  exact toSSet_I_rlp_mem_boundaryRLP hf hg

/-- The two boundary-RLP properties agree across the adjunction. -/
theorem boundaryRLP_eq_inverseImage_I_rlp :
    realizedBoundaryInclusions.rlp =
      (SSet.modelCategoryQuillen.I.rlp).inverseImage toSSet :=
  le_antisymm boundaryRLP_le_inverseImage_I_rlp
    inverseImage_I_rlp_le_boundaryRLP

end TopCat
