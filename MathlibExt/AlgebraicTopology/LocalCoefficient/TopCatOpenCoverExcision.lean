/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetWeakComponentCoefficients
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetSubcomplexExcision
public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatExcisionMap
public import MathlibExt.Topology.Category.TopCat.OpenCoverHomotopyPushout
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# Original local-coefficient excision on arbitrary open covers

The actual subordinate inclusion is weak by the existing two-open-set
comparison and realization counit. The original component coefficient
cofans then give its quasi-isomorphism for every integer local system,
without connectedness of the ambient space or flatness of the stalks.

The singular-subspace charts and original quotient projections identify
the actual topological excision map with the computed subcomplex map.
No excision quasi-isomorphism or source-system square is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped Simplicial

universe u

namespace TopCat

/-- The ACTUAL subordinate two-open-set inclusion is weak for arbitrary
ambient components. Its original realization/counit comparison is retained. -/
public theorem subordinateOpenCoverInclusion_mem_realizationWeakEquivalences
    (X : TopCat.{u}) (A B : TopologicalSpace.Opens X)
    (hcover : (A : Set X) ∪ B = Set.univ) :
    SSet.realizationWeakEquivalences
      ((subordinateSet (A : Set X) ⊔ subordinateSet (B : Set X)).ι) := by
  let K : (TopCat.toSSet.obj X).Subcomplex := subordinateSet (A : Set X) ⊔
      subordinateSet (B : Set X)
  let f : (K : SSet.{u}) ⟶ TopCat.toSSet.obj X := K.ι
  have hComposite : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map f ≫ sSetTopAdj.counit.app X) :=
    realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences A B hcover
  have hReal : TopCat.weakHomotopyEquivalences (SSet.toTop.map f) :=
    TopCat.weakHomotopyEquivalences.of_postcomp _ _
      (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences X) hComposite
  exact (SSet.mem_realizationWeakEquivalences_iff f).mpr
    ((TopCat.mem_weakHomotopyEquivalences_iff (SSet.toTop.map f)).mp hReal)

/-- The original cover inclusion gives a quasi-isomorphism for every
target integer system, with no ambient path-connectedness hypothesis. -/
public theorem quasiIso_localCoefficientCoverInclusion_allComponents
    (X : TopCat.{u}) (A B : TopologicalSpace.Opens X)
    (hcover : (A : Set X) ∪ B = Set.univ)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    QuasiIso (SSet.localCoefficientPullbackChainMap
      ((subordinateSet (A : Set X) ⊔ subordinateSet (B : Set X)).ι) L) :=
  SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap_allComponents
    _ (subordinateOpenCoverInclusion_mem_realizationWeakEquivalences X A B hcover) L

private theorem subcomplexMap_comp_ambient
    {T : SSet.{u}} (L : SSet.LocalSystem ℤ T)
    {U V : T.Subcomplex} (h : U ≤ V) :
    SSet.localCoefficientSubcomplexMap L h ≫ SSet.localCoefficientPullbackChainMap V.ι L =
      SSet.localCoefficientPullbackChainMap U.ι L := by
  rw [SSet.localCoefficientSubcomplexMap_eq]
  exact SSet.localCoefficientChainMapOver_comp _ _ _ _ L

private def subcomplexEqCoefficientIso
    {T : SSet.{u}} (L : SSet.LocalSystem ℤ T)
    {U V : T.Subcomplex} (h : U = V) :
    SSet.localCoefficientChainComplex (L.pullback U.ι) ≅
      SSet.localCoefficientChainComplex (L.pullback V.ι) := by
  let f := SSet.Subcomplex.homOfLE h.le
  letI : IsIso f := by
    change IsIso (SSet.Subcomplex.eqToIso h).hom
    infer_instance
  let q := SSet.localCoefficientSubcomplexMap L h.le
  have hq : IsIso q := by
    change IsIso (SSet.localCoefficientSubcomplexMap L h.le)
    rw [SSet.localCoefficientSubcomplexMap_eq]
    exact SSet.localCoefficientChainMapOver_isIso _ _ _ _ L
  exact @asIso _ _ _ _ q hq

private theorem subcomplexEqCoefficientIso_comp_ambient
    {T : SSet.{u}} (L : SSet.LocalSystem ℤ T)
    {U V : T.Subcomplex} (h : U = V) :
    (subcomplexEqCoefficientIso L h).hom ≫ SSet.localCoefficientPullbackChainMap V.ι L =
      SSet.localCoefficientPullbackChainMap U.ι L := by
  change SSet.localCoefficientSubcomplexMap L h.le ≫ _ = _
  exact subcomplexMap_comp_ambient L h.le

private theorem subordinateMap_comp_ambient
    {X : TopCat.{u}} {A B : Set X} (h : A ⊆ B)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    localCoefficientSubordinateMap h L ≫
        SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L =
      SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L := by
  let e := localCoefficientSubspaceChartMap A L
  let mA := SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L
  let mB := SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L
  let pA := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L
  let pB := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl B)) L
  let : IsIso e := localCoefficientSubspaceChartMap_isIso A L
  have hn : e ≫ localCoefficientSubordinateMap h L =
      localCoefficientSingularSubspaceMap h L ≫ localCoefficientSubspaceChartMap B L :=
    localCoefficientSubspaceChartMap_naturality h L
  have hB : localCoefficientSubspaceChartMap B L ≫ mB = pB :=
    localCoefficientSubspaceChartMap_comp B L
  have hA : e ≫ mA = pA := localCoefficientSubspaceChartMap_comp A L
  have hp : localCoefficientSingularSubspaceMap h L ≫ pB = pA := by
    rw [localCoefficientSingularSubspaceMap_eq]
    exact SSet.localCoefficientChainMapOver_comp _ _ _ _ L
  apply (cancel_epi e).1
  change e ≫ (localCoefficientSubordinateMap h L ≫ mB) = e ≫ mA
  rw [← Category.assoc, hn, Category.assoc, hB, hp, hA]

private def subordinateIntersectionCoefficientIso
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    SSet.localCoefficientChainComplex (L.pullback (subordinateSet (A ∩ B)).ι) ≅
      SSet.localCoefficientChainComplex
        (L.pullback (subordinateSet B ⊓ subordinateSet A).ι) :=
  subcomplexEqCoefficientIso L
    ((subordinateSet_inter A B).trans (inf_comm _ _))

private theorem subordinateIntersectionCoefficientIso_square
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    (subordinateIntersectionCoefficientIso X A B L).hom ≫
        SSet.localCoefficientSubcomplexMap L
          (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B) =
      localCoefficientSubordinateMap (Set.inter_subset_right : A ∩ B ⊆ B) L := by
  let p := SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L
  let : Mono p := SSet.localCoefficientPullbackChainMap_mono_of_mono _ L
  apply (cancel_mono p).mp
  change ((subordinateIntersectionCoefficientIso X A B L).hom ≫ _) ≫
      SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L =
    localCoefficientSubordinateMap (Set.inter_subset_right : A ∩ B ⊆ B) L ≫
      SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L
  rw [Category.assoc, subcomplexMap_comp_ambient]
  change (subcomplexEqCoefficientIso L
      ((subordinateSet_inter A B).trans (inf_comm _ _))).hom ≫
      SSet.localCoefficientPullbackChainMap (subordinateSet B ⊓ subordinateSet A).ι L = _
  rw [subcomplexEqCoefficientIso_comp_ambient, subordinateMap_comp_ambient]

private def subordinateExcisionSourceIso
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel (localCoefficientSubordinateMap (Set.inter_subset_right : A ∩ B ⊆ B) L) ≅
      cokernel (SSet.localCoefficientSubcomplexMap L
        (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)) := by
  let e := subordinateIntersectionCoefficientIso X A B L
  let a := localCoefficientSubordinateMap (Set.inter_subset_right : A ∩ B ⊆ B) L
  let m := SSet.localCoefficientSubcomplexMap L
    (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)
  exact cokernel.mapIso a m e
    (Iso.refl (SSet.localCoefficientChainComplex (L.pullback (subordinateSet B).ι))) (by
    rw [Iso.refl_hom, Category.comp_id]
    exact (subordinateIntersectionCoefficientIso_square X A B L).symm)

private theorem subordinateExcisionSourceIso_π
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientSubordinateMap (Set.inter_subset_right : A ∩ B ⊆ B) L) ≫
        (subordinateExcisionSourceIso X A B L).hom =
      cokernel.π (SSet.localCoefficientSubcomplexMap L
        (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)) := by
  simp only [subordinateExcisionSourceIso, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc, Iso.refl_hom, Category.id_comp]

private def actualExcisionSourceIso
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel (localCoefficientExcisionSourceArrow X A B L) ≅
      cokernel (SSet.localCoefficientSubcomplexMap L
        (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)) :=
  cokernelIsoOfEq (localCoefficientExcisionSourceArrow_eq X A B L) ≪≫
    localCoefficientSubspaceRelativeIso (Set.inter_subset_right : A ∩ B ⊆ B) L ≪≫
      subordinateExcisionSourceIso X A B L

private theorem actualExcisionSourceIso_π
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientExcisionSourceArrow X A B L) ≫
        (actualExcisionSourceIso X A B L).hom =
      localCoefficientSubspaceChartMap B L ≫
        cokernel.π (SSet.localCoefficientSubcomplexMap L
          (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)) := by
  let e0 := cokernelIsoOfEq (localCoefficientExcisionSourceArrow_eq X A B L)
  let e1 := localCoefficientSubspaceRelativeIso (Set.inter_subset_right : A ∩ B ⊆ B) L
  let e2 := subordinateExcisionSourceIso X A B L
  change cokernel.π _ ≫ (e0.hom ≫ e1.hom ≫ e2.hom) = _
  calc
    _ = (cokernel.π _ ≫ e0.hom) ≫ e1.hom ≫ e2.hom := by
      simp only [Category.assoc]
    _ = cokernel.π (localCoefficientSingularSubspaceMap
        (Set.inter_subset_right : A ∩ B ⊆ B) L) ≫ e1.hom ≫ e2.hom := by
      rw [π_comp_cokernelIsoOfEq_hom]
    _ = (localCoefficientSubspaceChartMap B L ≫
        cokernel.π (localCoefficientSubordinateMap
          (Set.inter_subset_right : A ∩ B ⊆ B) L)) ≫ e2.hom := by
      rw [← Category.assoc, localCoefficientSubspaceRelativeIso_π]
    _ = _ := by
      rw [Category.assoc, subordinateExcisionSourceIso_π]

private def subordinateExcisionTargetIso
    (X : TopCat.{u}) (A : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L) ≅
      cokernel (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L) := by
  let e := @asIso _ _ _ _ (localCoefficientSubspaceChartMap A L)
    (localCoefficientSubspaceChartMap_isIso A L)
  let a := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L
  let m := SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L
  exact cokernel.mapIso a m e (Iso.refl (SSet.localCoefficientChainComplex L)) (by
    rw [Iso.refl_hom, Category.comp_id]
    exact (localCoefficientSubspaceChartMap_comp A L).symm)

private theorem subordinateExcisionTargetIso_π
    (X : TopCat.{u}) (A : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl A)) L) ≫
        (subordinateExcisionTargetIso X A L).hom =
      cokernel.π (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L) := by
  simp only [subordinateExcisionTargetIso, cokernel.mapIso_hom, cokernel.map,
    cokernel.π_desc, Iso.refl_hom, Category.id_comp]

private def actualExcisionTargetIso
    (X : TopCat.{u}) (A : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel (localCoefficientExcisionTargetArrow X A L) ≅
      cokernel (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L) :=
  cokernelIsoOfEq (localCoefficientExcisionTargetArrow_eq X A L) ≪≫
    subordinateExcisionTargetIso X A L

private theorem actualExcisionTargetIso_π
    (X : TopCat.{u}) (A : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientExcisionTargetArrow X A L) ≫
        (actualExcisionTargetIso X A L).hom =
      cokernel.π (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L) := by
  change cokernel.π _ ≫
    ((cokernelIsoOfEq (localCoefficientExcisionTargetArrow_eq X A L)).hom ≫
      (subordinateExcisionTargetIso X A L).hom) = _
  rw [← Category.assoc, π_comp_cokernelIsoOfEq_hom, subordinateExcisionTargetIso_π]

private theorem actualExcision_original_square
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    (actualExcisionSourceIso X A B L).hom ≫
        SSet.localCoefficientSubcomplexExcisionMap L (subordinateSet B) (subordinateSet A) =
      localCoefficientExcisionChainMap X A B L ≫ (actualExcisionTargetIso X A L).hom := by
  let q := cokernel.π (localCoefficientExcisionSourceArrow X A B L)
  let b := SSet.localCoefficientPullbackChainMap (TopCat.toSSet.map (subspaceIncl B)) L
  let p := SSet.localCoefficientPullbackChainMap (subordinateSet B).ι L
  let t := cokernel.π (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L)
  let eS := actualExcisionSourceIso X A B L
  let eT := actualExcisionTargetIso X A L
  let m := SSet.localCoefficientSubcomplexExcisionMap L (subordinateSet B) (subordinateSet A)
  apply (cancel_epi q).mp
  change q ≫ (eS.hom ≫ m) = q ≫ (localCoefficientExcisionChainMap X A B L ≫ eT.hom)
  calc
    _ = (q ≫ eS.hom) ≫ m := (Category.assoc _ _ _).symm
    _ = (localCoefficientSubspaceChartMap B L ≫
        cokernel.π (SSet.localCoefficientSubcomplexMap L
          (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B))) ≫ m :=
      congrArg (fun k => k ≫ m) (actualExcisionSourceIso_π X A B L)
    _ = localCoefficientSubspaceChartMap B L ≫ (p ≫ t) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => localCoefficientSubspaceChartMap B L ≫ k)
           (SSet.localCoefficientSubcomplexExcisionMap_π L (subordinateSet B) (subordinateSet A)))
    _ = (localCoefficientSubspaceChartMap B L ≫ p) ≫ t := (Category.assoc _ _ _).symm
    _ = b ≫ t := congrArg (fun k => k ≫ t) (localCoefficientSubspaceChartMap_comp B L)
    _ = b ≫ (cokernel.π (localCoefficientExcisionTargetArrow X A L) ≫ eT.hom) :=
      congrArg (fun k => b ≫ k) (actualExcisionTargetIso_π X A L).symm
    _ = (b ≫ cokernel.π (localCoefficientExcisionTargetArrow X A L)) ≫ eT.hom :=
      (Category.assoc _ _ _).symm
    _ = (q ≫ localCoefficientExcisionChainMap X A B L) ≫ eT.hom :=
      congrArg (fun k => k ≫ eT.hom) (localCoefficientExcisionChainMap_π X A B L).symm
    _ = _ := Category.assoc _ _ _

/-- A computed arrow Iso identifies the ACTUAL topological excision map
with the original subordinate-complex excision map. Both endpoints use the
same target system, its original pullbacks, and their quotient projections. -/
public def localCoefficientExcisionComparisonIso
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    Arrow.mk (localCoefficientExcisionChainMap X A B L) ≅
      Arrow.mk (SSet.localCoefficientSubcomplexExcisionMap L
        (subordinateSet B) (subordinateSet A)) :=
  Arrow.isoMk (actualExcisionSourceIso X A B L) (actualExcisionTargetIso X A L)
    (actualExcision_original_square X A B L)

/-- The source chart keeps the actual B coefficient chart and the whole
original quotient projection. -/
@[reassoc]
public theorem localCoefficientExcisionComparisonIso_source_π
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientExcisionSourceArrow X A B L) ≫
        (localCoefficientExcisionComparisonIso X A B L).hom.left =
      localCoefficientSubspaceChartMap B L ≫
        cokernel.π (SSet.localCoefficientSubcomplexMap L
          (inf_le_left : subordinateSet B ⊓ subordinateSet A ≤ subordinateSet B)) :=
  actualExcisionSourceIso_π X A B L

/-- The target chart keeps the literal ambient quotient projection. -/
@[reassoc]
public theorem localCoefficientExcisionComparisonIso_target_π
    (X : TopCat.{u}) (A B : Set X)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    cokernel.π (localCoefficientExcisionTargetArrow X A L) ≫
        (localCoefficientExcisionComparisonIso X A B L).hom.right =
      cokernel.π (SSet.localCoefficientPullbackChainMap (subordinateSet A).ι L) :=
  actualExcisionTargetIso_π X A L

/-- Excision holds for the ACTUAL original relative map (B,A∩B)→(X,A)
and every target integer local system on an arbitrary two-open-set cover.
The source weak comparison, component quasi-isomorphisms, exact integer
coproduct, and both original quotient charts are derived in the proof. -/
public theorem localCoefficientExcisionChainMap_quasiIso_of_openCover
    (X : TopCat.{u}) (A B : TopologicalSpace.Opens X)
    (hcover : (A : Set X) ∪ B = Set.univ)
    (L : SSet.LocalSystem ℤ (TopCat.toSSet.obj X)) :
    QuasiIso (localCoefficientExcisionChainMap X A B L) := by
  have hUnion : QuasiIso (SSet.localCoefficientPullbackChainMap
      ((subordinateSet (B : Set X) ⊔ subordinateSet (A : Set X)).ι) L) :=
    quasiIso_localCoefficientCoverInclusion_allComponents X B A
      ((Set.union_comm _ _).trans hcover) L
  have hSub : QuasiIso (SSet.localCoefficientSubcomplexExcisionMap L
      (subordinateSet (B : Set X)) (subordinateSet (A : Set X))) :=
    SSet.localCoefficientSubcomplexExcisionMap_quasiIso L _ _ hUnion
  exact (_root_.quasiIso_iff_of_arrow_mk_iso _ _
    (localCoefficientExcisionComparisonIso X A B L)).mpr hSub

/-- The same actual excision map for every original topological integer
local system. The canonical singular fundamental-groupoid pullback keeps
all source coefficient transports; no flatness hypothesis is imposed. -/
public theorem localCoefficientExcisionChainMap_toSingular_quasiIso_of_openCover
    (X : TopCat.{u}) (A B : TopologicalSpace.Opens X)
    (hcover : (A : Set X) ∪ B = Set.univ) (L : TopCat.LocalSystem ℤ X) :
    QuasiIso (localCoefficientExcisionChainMap X A B L.toSingular) :=
  localCoefficientExcisionChainMap_quasiIso_of_openCover X A B hcover L.toSingular

end TopCat

end
