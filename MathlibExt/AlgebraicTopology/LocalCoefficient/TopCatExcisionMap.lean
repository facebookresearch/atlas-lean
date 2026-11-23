/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatSubspaceChains
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology

/-!
# The actual topological excision map with target local systems

The source is the original local-system relative chain complex of
(B,A∩B), and the target is the original relative complex of (X,A).
Both inherit the SAME system on Sing X. The map is computed by the actual
singular subspace maps and the stock cokernel map. Its full quotient square
is derived; no excision quasi-isomorphism is assumed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace TopCat

variable (X : TopCat.{u}) (A B : Set X)
  (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X))

/-- The actual original coefficient source relative arrow A∩B→B. -/
public def localCoefficientExcisionSourceArrow :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl (A ∩ B)))) ⟶
      SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl B))) :=
  localCoefficientSingularSubspaceMap (Set.inter_subset_right : A ∩ B ⊆ B) L

omit B in
/-- The actual original coefficient target relative arrow A→X. -/
public def localCoefficientExcisionTargetArrow :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl A))) ⟶
      SSet.localCoefficientChainComplex L :=
  SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L

/-- The actual source arrow has the original nested-subspace map as its
computed value. This characteristic permits downstream quotient transport
without unfolding the public arrow. -/
public theorem localCoefficientExcisionSourceArrow_eq :
    localCoefficientExcisionSourceArrow X A B L =
       localCoefficientSingularSubspaceMap (Set.inter_subset_right : A ∩ B ⊆ B) L := by
  unfold localCoefficientExcisionSourceArrow
  rfl

omit B in
/-- The actual target arrow has the original ambient inclusion map as its
computed value. -/
public theorem localCoefficientExcisionTargetArrow_eq :
    localCoefficientExcisionTargetArrow X A L =
       SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L := by
  unfold localCoefficientExcisionTargetArrow
  rfl

/-- The actual excision square uses the original subspace map A∩B→A and
original ambient map B→X, with no desired chain compatibility input. -/
public theorem localCoefficientExcisionSquare :
    localCoefficientSingularSubspaceMap (Set.inter_subset_left : A ∩ B ⊆ A) L ≫
        localCoefficientExcisionTargetArrow X A L =
      localCoefficientExcisionSourceArrow X A B L ≫
        SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl B)) L := by
  rw [localCoefficientExcisionSourceArrow_eq X A B L,
    localCoefficientExcisionTargetArrow_eq X A L,
    localCoefficientSingularSubspaceMap_eq (Set.inter_subset_left : A ∩ B ⊆ A) L,
    localCoefficientSingularSubspaceMap_eq (Set.inter_subset_right : A ∩ B ⊆ B) L,
    SSet.localCoefficientChainMapOver_comp, SSet.localCoefficientChainMapOver_comp]

/-- The actual target-local-system excision map on original relative
chains, computed from the original topological maps. -/
public def localCoefficientExcisionChainMap :
    cokernel (localCoefficientExcisionSourceArrow X A B L) ⟶
      cokernel (localCoefficientExcisionTargetArrow X A L) :=
  cokernel.map _ _
    (localCoefficientSingularSubspaceMap (Set.inter_subset_left : A ∩ B ⊆ A) L)
    (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl B)) L)
    (localCoefficientExcisionSquare X A B L).symm

/-- The whole original quotient square certifies the actual excision map. -/
@[reassoc]
public theorem localCoefficientExcisionChainMap_π :
    cokernel.π (localCoefficientExcisionSourceArrow X A B L) ≫
        localCoefficientExcisionChainMap X A B L =
      SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl B)) L ≫
        cokernel.π (localCoefficientExcisionTargetArrow X A L) := by
  unfold localCoefficientExcisionChainMap
  exact cokernel.π_desc _ _ _

end TopCat

end
