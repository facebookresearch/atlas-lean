/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SingularHomology.Subspace.Basic
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetPullbackIsomorphism
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The actual singular subspace dictionary with original local systems

The existing singular range comparison identifies the singular subspace
with the subordinate simplicial set. Original pullback-composition and
congruence transports then give the actual coefficient-chain Iso and its
whole ambient inclusion triangle. Constant coefficient naturality is not
used as a varying local-system theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

namespace TopCat

variable {X : TopCat.{u}}

private local instance localCoefficientComplexMapHasCokernel
    {K D : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ D) :
    HasCokernel f := inferInstance

/-- The actual singular-subspace range Iso, using the existing range
equality. This is the same comparison used by the open-cover owner. -/
public def localCoefficientSingularSubspaceIso (S : Set X) :
    TopCat.toSSet.obj (TopCat.of S) ≅ (subordinateSet S : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map (subspaceIncl S))) ≪≫
    SSet.Subcomplex.eqToIso (range_subspaceIncl_eq_subordinateSet S)

/-- The actual simplicial chart retains the original subspace inclusion. -/
@[reassoc]
public theorem localCoefficientSingularSubspaceIso_hom_ι (S : Set X) :
    (localCoefficientSingularSubspaceIso S).hom ≫ (subordinateSet S).ι =
      TopCat.toSSet.map (subspaceIncl S) := by
  simp [localCoefficientSingularSubspaceIso]

/-- The ACTUAL coefficient-chain map from singular subspace to its
subordinate complex, over the same ambient singular coefficient system. -/
public def localCoefficientSubspaceChartMap (S : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl S))) ⟶
      SSet.localCoefficientChainComplex (L.pullback (subordinateSet S).ι) :=
  SSet.localCoefficientChainMapOver (localCoefficientSingularSubspaceIso S).hom
    (subordinateSet S).ι (TopCat.toSSet.map (subspaceIncl S))
    (localCoefficientSingularSubspaceIso_hom_ι S).symm L

/-- The original coefficient subspace chart is an Iso, with no given
coefficient comparison or weak model witness. -/
public theorem localCoefficientSubspaceChartMap_isIso (S : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    IsIso (localCoefficientSubspaceChartMap S L) :=
  SSet.localCoefficientChainMapOver_isIso (localCoefficientSingularSubspaceIso S).hom
    (subordinateSet S).ι (TopCat.toSSet.map (subspaceIncl S))
    (localCoefficientSingularSubspaceIso_hom_ι S).symm L

/-- The chart's WHOLE original ambient coefficient triangle commutes. -/
@[reassoc]
public theorem localCoefficientSubspaceChartMap_comp (S : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    localCoefficientSubspaceChartMap S L ≫
        SSet.localCoefficientPullbackChainMap (subordinateSet S).ι L =
      SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl S)) L :=
  SSet.localCoefficientChainMapOver_comp (localCoefficientSingularSubspaceIso S).hom
    (subordinateSet S).ι (TopCat.toSSet.map (subspaceIncl S))
    (localCoefficientSingularSubspaceIso_hom_ι S).symm L

/-- The actual original coefficient map between nested singular subspaces,
written over the same ambient singular coefficient base. -/
public def localCoefficientSingularSubspaceMap {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl S))) ⟶
      SSet.localCoefficientChainComplex
        (L.pullback (TopCat.toSSet.map (subspaceIncl T))) :=
  SSet.localCoefficientChainMapOver (TopCat.toSSet.map (subspaceInclOfSubset h))
    (TopCat.toSSet.map (subspaceIncl T)) (TopCat.toSSet.map (subspaceIncl S))
    (by rw [← TopCat.toSSet.map_comp, subspaceInclOfSubset_comp]) L

public theorem localCoefficientSingularSubspaceMap_eq {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    localCoefficientSingularSubspaceMap h L =
      SSet.localCoefficientChainMapOver (TopCat.toSSet.map (subspaceInclOfSubset h))
        (TopCat.toSSet.map (subspaceIncl T)) (TopCat.toSSet.map (subspaceIncl S))
        (by rw [← TopCat.toSSet.map_comp, subspaceInclOfSubset_comp]) L := by
  unfold localCoefficientSingularSubspaceMap
  rfl

/-- The actual original coefficient map between nested subordinate
subcomplexes, written over the same ambient singular coefficient base. -/
public def localCoefficientSubordinateMap {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    SSet.localCoefficientChainComplex (L.pullback (subordinateSet S).ι) ⟶
      SSet.localCoefficientChainComplex (L.pullback (subordinateSet T).ι) :=
  SSet.localCoefficientChainMapOver
    (SSet.Subcomplex.homOfLE (subordinateSet_mono h))
    (subordinateSet T).ι (subordinateSet S).ι
    (by rw [SSet.Subcomplex.homOfLE_ι]) L

/-- The actual coefficient subspace chart is natural for nested
subspaces. The WHOLE square is derived by cancelling the original mono
ambient coefficient map and using the original source triangles. -/
public theorem localCoefficientSubspaceChartMap_naturality
    {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    localCoefficientSubspaceChartMap S L ≫ localCoefficientSubordinateMap h L =
      localCoefficientSingularSubspaceMap h L ≫ localCoefficientSubspaceChartMap T L := by
  let m := SSet.localCoefficientPullbackChainMap (subordinateSet T).ι L
  let : Mono m := SSet.localCoefficientPullbackChainMap_mono_of_mono _ L
  apply (cancel_mono m).mp
  change (localCoefficientSubspaceChartMap S L ≫ localCoefficientSubordinateMap h L) ≫
      SSet.localCoefficientPullbackChainMap (subordinateSet T).ι L =
    (localCoefficientSingularSubspaceMap h L ≫ localCoefficientSubspaceChartMap T L) ≫
      SSet.localCoefficientPullbackChainMap (subordinateSet T).ι L
  rw [Category.assoc]
  unfold localCoefficientSubordinateMap
  rw [SSet.localCoefficientChainMapOver_comp, localCoefficientSubspaceChartMap_comp]
  rw [Category.assoc, localCoefficientSubspaceChartMap_comp]
  unfold localCoefficientSingularSubspaceMap
  rw [SSet.localCoefficientChainMapOver_comp]

/-- The actual relative original singular-subspace chains agree with the
actual subordinate relative chains through their derived coefficient
charts and WHOLE map square. -/
public def localCoefficientSubspaceRelativeIso
    {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel (localCoefficientSingularSubspaceMap h L) ≅
      cokernel (localCoefficientSubordinateMap h L) := by
  let a := localCoefficientSingularSubspaceMap h L
  let b := localCoefficientSubordinateMap h L
  let eS : SSet.localCoefficientChainComplex
      (L.pullback (TopCat.toSSet.map (subspaceIncl S))) ≅
      SSet.localCoefficientChainComplex (L.pullback (subordinateSet S).ι) :=
    @asIso _ _ _ _ (localCoefficientSubspaceChartMap S L)
    (localCoefficientSubspaceChartMap_isIso S L)
  let eT : SSet.localCoefficientChainComplex
      (L.pullback (TopCat.toSSet.map (subspaceIncl T))) ≅
      SSet.localCoefficientChainComplex (L.pullback (subordinateSet T).ι) :=
    @asIso _ _ _ _ (localCoefficientSubspaceChartMap T L)
    (localCoefficientSubspaceChartMap_isIso T L)
  exact cokernel.mapIso a b eS eT
    (localCoefficientSubspaceChartMap_naturality h L).symm

/-- The relative subspace chart retains the exact original target
coefficient chart and actual quotient projection. -/
@[reassoc]
public theorem localCoefficientSubspaceRelativeIso_π
    {S T : Set X} (h : S ⊆ T)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientSingularSubspaceMap h L) ≫
      (localCoefficientSubspaceRelativeIso h L).hom =
    localCoefficientSubspaceChartMap T L ≫
      cokernel.π (localCoefficientSubordinateMap h L) := by
  unfold localCoefficientSubspaceRelativeIso
  exact cokernel.π_desc _ _ _

end TopCat

end
