/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationLifting
public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CartesianMonoidalModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationProduct
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHModelStructure
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHPointCofibrant
public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Multifunctor

/-!
# The cartesian monoidal model structure on CGWH

The selected weak-homotopy model structure on compactly generated weak
Hausdorff spaces satisfies the pushout-product and unit axioms for the
selected cartesian closed structure.  The instances are opt-in through the
`CGWH.modelCategory` scope.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory CategoryTheory.Functor
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory SSet.modelCategoryQuillen CGWH.modelCategory

namespace CGWH.modelCategory

/-- The canonical braiding induced by the cartesian monoidal structure. -/
noncomputable scoped instance instBraidedCategory :
    BraidedCategory CGWH.{u, v} :=
  BraidedCategory.ofCartesianMonoidalCategory

private noncomputable def cgwhRealizationTensorNatIso :
    curriedTensorPost SSet.toCGWH.{u, v} ≅ curriedTensorPre SSet.toCGWH.{u, v} :=
  CartesianMonoidalCategory.prodComparisonBifunctorNatIso SSet.toCGWH.{u, v}

private noncomputable def cgwhRealizationPushoutProductIso
    {A B K L : SSet.{v}} (i : A ⟶ B) (j : K ⟶ L) :
    SSet.toCGWH.{u, v}.mapArrow.obj (Arrow.mk i □ Arrow.mk j) ≅
      Arrow.mk (SSet.toCGWH.{u, v}.map i) □ Arrow.mk (SSet.toCGWH.{u, v}.map j) := by
  let _ : SSet.toCGWH.{u, v}.IsLeftAdjoint := SSet.sSetCGWHAdj.isLeftAdjoint
  let sq := PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i j
  let mappedSq : (curriedTensorPost SSet.toCGWH.{u, v}).PushoutObjObj i j :=
    { pt := SSet.toCGWH.{u, v}.obj sq.pt
      inl := SSet.toCGWH.{u, v}.map sq.inl
      inr := SSet.toCGWH.{u, v}.map sq.inr
      isPushout := SSet.toCGWH.{u, v}.map_isPushout sq.isPushout
      ι := SSet.toCGWH.{u, v}.map sq.ι
      inl_ι := by
        rw [← SSet.toCGWH.{u, v}.map_comp, sq.inl_ι]
        rfl
      inr_ι := by
        rw [← SSet.toCGWH.{u, v}.map_comp, sq.inr_ι]
        rfl }
  let targetSq := mappedSq.ofNatIso cgwhRealizationTensorNatIso
  let standardSq := PushoutObjObj.ofHasPushout
    (curriedTensorPre SSet.toCGWH.{u, v}) i j
  let eLeft := targetSq.isPushout.isoIsPushout _ _ standardSq.isPushout
  change Arrow.mk (SSet.toCGWH.{u, v}.map sq.ι) ≅ Arrow.mk standardSq.ι
  have hι : eLeft.hom ≫ standardSq.ι = targetSq.ι := by
    apply targetSq.isPushout.hom_ext
    · rw [targetSq.isPushout.inl_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout]
      rw [standardSq.inl_ι]
      exact targetSq.inl_ι.symm
    · rw [targetSq.isPushout.inr_isoIsPushout_hom_assoc
        _ _ standardSq.isPushout]
      rw [standardSq.inr_ι]
      exact targetSq.inr_ι.symm
  refine Arrow.isoMk eLeft
    ((cgwhRealizationTensorNatIso.app B).app L) ?_
  change eLeft.hom ≫ standardSq.ι =
    SSet.toCGWH.{u, v}.map sq.ι ≫ ((cgwhRealizationTensorNatIso.hom.app B).app L)
  exact hι

private theorem cgwhCartesianFreeCofibrationCofibration
    {A B K L : CGWH.{u, v}} (i : A ⟶ B)
    (hi : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) i) (j : K ⟶ L)
    (hj : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) j) :
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      let _ : Cofibration f :=
        (HomotopicalAlgebra.cofibration_iff f).mpr hi
      let _ : Cofibration g :=
        (HomotopicalAlgebra.cofibration_iff g).mpr hj
      have hSource : cofibrations SSet.{v}
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        (HomotopicalAlgebra.cofibration_iff _).mp
          (SSet.cofibration_pushoutProduct f g)
      have hMapped : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
          (SSet.toCGWH.{u, v}.map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (cofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} _ hSource
      have hOrth := ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp
        _ hMapped
      exact (((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp.arrow_iso_iff
        (cgwhRealizationPushoutProductIso f g)).mp hOrth

private theorem cgwhCartesianFreeTrivialCofibrationLeft
    {A B K L : CGWH.{u, v}} (i : A ⟶ B)
    (hi : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) i) (j : K ⟶ L)
    (hj : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) j) :
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      let _ : Cofibration f := (mem_trivialCofibrations_iff f).mp hi |>.1
      let _ : WeakEquivalence f :=
        (mem_trivialCofibrations_iff f).mp hi |>.2
      let _ : Cofibration g :=
        (HomotopicalAlgebra.cofibration_iff g).mpr hj
      have hSource : trivialCofibrations SSet.{v}
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        SSet.pushoutProduct_mem_trivialCofibrations_of_left f g
      have hMapped : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
          (SSet.toCGWH.{u, v}.map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (trivialCofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} _ hSource
      have hOrth :=
        ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp
          _ hMapped
      exact
        (((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp.arrow_iso_iff
          (cgwhRealizationPushoutProductIso f g)).mp hOrth

private theorem cgwhCartesianFreeTrivialCofibrationRight
    {A B K L : CGWH.{u, v}} (i : A ⟶ B)
    (hi : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) i) (j : K ⟶ L)
    (hj : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}) j) :
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      let _ : Cofibration f :=
        (HomotopicalAlgebra.cofibration_iff f).mpr hi
      let _ : Cofibration g := (mem_trivialCofibrations_iff g).mp hj |>.1
      let _ : WeakEquivalence g :=
        (mem_trivialCofibrations_iff g).mp hj |>.2
      have hSource : trivialCofibrations SSet.{v}
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        SSet.pushoutProduct_mem_trivialCofibrations_of_right f g
      have hMapped : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
          (SSet.toCGWH.{u, v}.map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (trivialCofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} _ hSource
      have hOrth :=
        ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp
          _ hMapped
      exact
        (((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp.arrow_iso_iff
          (cgwhRealizationPushoutProductIso f g)).mp hOrth

private theorem cgwhCartesianCofibrationPushoutProduct
    {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations CGWH.{u, v} i)
    (hj : cofibrations CGWH.{u, v} j) :
    cofibrations CGWH.{u, v} ((Arrow.mk i □ Arrow.mk j).hom) := by
  have hi' : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp i := by
    rw [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hi
  have hj' : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp j := by
    rw [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    (fun ⦃X Y W Z⦄ a ha b hb =>
      cgwhCartesianFreeCofibrationCofibration a ha b hb) hi' hj'
  rwa [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp] at h

private theorem cgwhCartesianTrivialPushoutProductLeft
    {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L)
    (hi : trivialCofibrations CGWH.{u, v} i)
    (hj : cofibrations CGWH.{u, v} j) :
    trivialCofibrations CGWH.{u, v}
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  have hi' : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp i := by
    rw [cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp]
    exact hi
  have hj' : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp j := by
    rw [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    (fun ⦃X Y W Z⦄ a ha b hb =>
      cgwhCartesianFreeTrivialCofibrationLeft a ha b hb) hi' hj'
  rwa [cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp] at h

private theorem cgwhCartesianTrivialPushoutProductRight
    {A B K L : CGWH.{u, v}} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations CGWH.{u, v} i)
    (hj : trivialCofibrations CGWH.{u, v} j) :
    trivialCofibrations CGWH.{u, v}
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  have hi' : ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp i := by
    rw [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hi
  have hj' : ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).rlp.llp j := by
    rw [cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v})
    (fun ⦃X Y W Z⦄ a ha b hb =>
      cgwhCartesianFreeTrivialCofibrationRight a ha b hb) hi' hj'
  rwa [cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp] at h

/-- The cartesian tensor unit is cofibrant in the selected CGWH model
structure. -/
theorem tensorUnit_isCofibrant :
    IsCofibrant (𝟙_ CGWH.{u, v}) := by
  let e : CGWH.point.{u, v} ≅ 𝟙_ CGWH.{u, v} :=
    CGWH.point_isTerminal.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
  let eArrow : Arrow.mk (initial.to CGWH.point.{u, v}) ≅
      Arrow.mk (initial.to (𝟙_ CGWH.{u, v})) :=
    Arrow.isoMk (Iso.refl _) e (initialIsInitial.hom_ext _ _)
  rw [isCofibrant_iff, HomotopicalAlgebra.cofibration_iff]
  apply ((cofibrations CGWH.{u, v}).arrow_mk_iso_iff eArrow).mp
  rw [← HomotopicalAlgebra.cofibration_iff, ← isCofibrant_iff]
  exact CGWH.point_isCofibrant

/-- The selected CGWH weak-homotopy model satisfies Hovey's cartesian
pushout-product and unit axioms. -/
noncomputable scoped instance instIsClosedSymmetricMonoidalModelCategory :
    IsClosedSymmetricMonoidalModelCategory CGWH.{u, v} := by
  let _ : IsCofibrant (𝟙_ CGWH.{u, v}) :=
    tensorUnit_isCofibrant
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    CGWH.{u, v}
    cgwhCartesianCofibrationPushoutProduct
    cgwhCartesianTrivialPushoutProductLeft
    cgwhCartesianTrivialPushoutProductRight

end CGWH.modelCategory
