/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.NativeProduct
public import MathlibExt.AlgebraicTopology.PlusConstruction.PointRelativeMapping
public import MathlibExt.Topology.Category.CGWH.RealizedProductPoint
public import MathlibExt.Topology.Homotopy.CGWHHSpaceFundamentalGroup
public import MathlibExt.GroupTheory.PerfectHomomorphism

/-!
# Derived multiplication and both unit families on an actual native plus

The actual native product-plus map supplies the extension domain. Its
perfect subgroup is killed by the whole original multiplication into
the commutative target fundamental group. Point cofibrations and all CW
models are derived from the original realized vertices. The original
source axis families and point-relative plus uniqueness then give both
whole unit families on the actual target. No target multiplication,
target unit family, product-plus witness, or CW model is input.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped TopCat.modelCategory ContinuousMap Simplicial

universe u

namespace CGWH

private def leftAxis (A : CGWH.{u, u}) (a : A) : A ⟶ A ⨯ A :=
  Limits.prod.lift (constMap A A a) (𝟙 A)

private def rightAxis (A : CGWH.{u, u}) (a : A) : A ⟶ A ⨯ A :=
  Limits.prod.lift (𝟙 A) (constMap A A a)

private theorem leftAxis_apply (A : CGWH.{u, u}) (a z : A) :
    leftAxis A a z = tensorMk a z :=
  (prod_lift_apply (constMap A A a) (𝟙 A) z).trans (tensorMk_eq_prodPoint a z).symm

private theorem rightAxis_apply (A : CGWH.{u, u}) (a z : A) :
    rightAxis A a z = tensorMk z a :=
  (prod_lift_apply (𝟙 A) (constMap A A a) z).trans (tensorMk_eq_prodPoint z a).symm

private theorem leftAxis_naturality {A M : CGWH.{u, u}}
    (q : A ⟶ M) (a : A) (m : M) (hq : q a = m) :
    leftAxis A a ≫ (q ⊗ₘ q) = q ≫ leftAxis M m := by
  apply ConcreteCategory.hom_ext
  intro z
  change (q ⊗ₘ q) (leftAxis A a z) = leftAxis M m (q z)
  exact (congrArg (q ⊗ₘ q) (leftAxis_apply A a z)).trans
    ((tensorMk_map q q a z).trans
      ((congrArg (fun p : M => tensorMk p (q z)) hq).trans
        (leftAxis_apply M m (q z)).symm))

private theorem rightAxis_naturality {A M : CGWH.{u, u}}
    (q : A ⟶ M) (a : A) (m : M) (hq : q a = m) :
    rightAxis A a ≫ (q ⊗ₘ q) = q ≫ rightAxis M m := by
  apply ConcreteCategory.hom_ext
  intro z
  change (q ⊗ₘ q) (rightAxis A a z) = rightAxis M m (q z)
  exact (congrArg (q ⊗ₘ q) (rightAxis_apply A a z)).trans
    ((tensorMk_map q q z a).trans
      ((congrArg (fun p : M => tensorMk (q z) p) hq).trans
        (rightAxis_apply M m (q z)).symm))

private def leftUnit_sourceTriangle {A M : CGWH.{u, u}}
    (q : A ⟶ M) (a : A) (m : M) (hq : q a = m)
    (muA : A ⨯ A ⟶ A) (muM : M ⨯ M ⟶ M)
    (K : ContinuousMap.HomotopyRel
      (cgwhToTop.map ((q ⊗ₘ q) ≫ muM)).hom
      (cgwhToTop.map (muA ≫ q)).hom {tensorMk a a})
    (L : ContinuousMap.HomotopyRel (cgwhToTop.map q).hom
      (cgwhToTop.map (hspaceLeftUnitMap A muA a ≫ q)).hom {a}) :
    ContinuousMap.HomotopyRel
      (cgwhToTop.map q ≫ cgwhToTop.map (hspaceLeftUnitMap M muM m)).hom
      (cgwhToTop.map q).hom {a} := by
  let R := K.precomposePointRelative (cgwhToTop.map (leftAxis A a)).hom a
    (leftAxis_apply A a a)
  have hs : (cgwhToTop.map ((q ⊗ₘ q) ≫ muM)).hom.comp
      (cgwhToTop.map (leftAxis A a)).hom =
        (cgwhToTop.map (q ≫ hspaceLeftUnitMap M muM m)).hom := by
    apply ContinuousMap.ext
    intro z
    change muM ((q ⊗ₘ q) (leftAxis A a z)) =
      (hspaceLeftUnitMap M muM m) (q z)
    have hn := ConcreteCategory.congr_hom (leftAxis_naturality q a m hq) z
    change (q ⊗ₘ q) (leftAxis A a z) = leftAxis M m (q z) at hn
    exact (congrArg muM hn).trans
      ((congrArg muM (prod_lift_apply (constMap M M m) (𝟙 M) (q z))).trans
        (hspaceLeftUnitMap_apply M muM m (q z)).symm)
  have ht : (cgwhToTop.map (muA ≫ q)).hom.comp
      (cgwhToTop.map (leftAxis A a)).hom =
        (cgwhToTop.map (hspaceLeftUnitMap A muA a ≫ q)).hom := by
    apply ContinuousMap.ext
    intro z
    change q (muA (leftAxis A a z)) = q ((hspaceLeftUnitMap A muA a) z)
    exact congrArg q ((congrArg muA
      (prod_lift_apply (constMap A A a) (𝟙 A) z)).trans
        (hspaceLeftUnitMap_apply A muA a z).symm)
  exact ((R.cast hs ht).trans L.symm).cast
    (congrArg TopCat.Hom.hom (cgwhToTop.map_comp q (hspaceLeftUnitMap M muM m))) rfl

private def rightUnit_sourceTriangle {A M : CGWH.{u, u}}
    (q : A ⟶ M) (a : A) (m : M) (hq : q a = m)
    (muA : A ⨯ A ⟶ A) (muM : M ⨯ M ⟶ M)
    (K : ContinuousMap.HomotopyRel
      (cgwhToTop.map ((q ⊗ₘ q) ≫ muM)).hom
      (cgwhToTop.map (muA ≫ q)).hom {tensorMk a a})
    (L : ContinuousMap.HomotopyRel (cgwhToTop.map q).hom
      (cgwhToTop.map (hspaceRightUnitMap A muA a ≫ q)).hom {a}) :
    ContinuousMap.HomotopyRel
      (cgwhToTop.map q ≫ cgwhToTop.map (hspaceRightUnitMap M muM m)).hom
      (cgwhToTop.map q).hom {a} := by
  let R := K.precomposePointRelative (cgwhToTop.map (rightAxis A a)).hom a
    (rightAxis_apply A a a)
  have hs : (cgwhToTop.map ((q ⊗ₘ q) ≫ muM)).hom.comp
      (cgwhToTop.map (rightAxis A a)).hom =
        (cgwhToTop.map (q ≫ hspaceRightUnitMap M muM m)).hom := by
    apply ContinuousMap.ext
    intro z
    change muM ((q ⊗ₘ q) (rightAxis A a z)) =
      (hspaceRightUnitMap M muM m) (q z)
    have hn := ConcreteCategory.congr_hom (rightAxis_naturality q a m hq) z
    change (q ⊗ₘ q) (rightAxis A a z) = rightAxis M m (q z) at hn
    exact (congrArg muM hn).trans
      ((congrArg muM (prod_lift_apply (𝟙 M) (constMap M M m) (q z))).trans
        (hspaceRightUnitMap_apply M muM m (q z)).symm)
  have ht : (cgwhToTop.map (muA ≫ q)).hom.comp
      (cgwhToTop.map (rightAxis A a)).hom =
        (cgwhToTop.map (hspaceRightUnitMap A muA a ≫ q)).hom := by
    apply ContinuousMap.ext
    intro z
    change q (muA (rightAxis A a z)) = q ((hspaceRightUnitMap A muA a) z)
    exact congrArg q ((congrArg muA
      (prod_lift_apply (𝟙 A) (constMap A A a) z)).trans
        (hspaceRightUnitMap_apply A muA a z).symm)
  exact ((R.cast hs ht).trans L.symm).cast
    (congrArg TopCat.Hom.hom (cgwhToTop.map_comp q (hspaceRightUnitMap M muM m))) rfl

private theorem tensorPoint_cofibration (A B : CGWH.{u, u}) (a : A) (b : B)
    (hSource : Cofibration (TopCat.const (prodPoint A B a b) :
      TopCat.of PUnit.{u + 1} ⟶ (A ⨯ B).toTop)) :
    Cofibration (TopCat.const (tensorMk a b) :
      TopCat.of PUnit.{u + 1} ⟶ (A ⊗ B : CGWH.{u, u}).toTop) := by
  let E := tensorSelectedProductIso A B
  let T : (A ⊗ B : CGWH.{u, u}).toTop ≅ (A ⨯ B).toTop := cgwhToTop.mapIso E
  let t : (A ⊗ B : CGWH.{u, u}) := tensorMk a b
  let p : (A ⨯ B : CGWH.{u, u}) := prodPoint A B a b
  have hPair : prodComparisonToTop A B (E.hom t) = (a, b) := by
    apply Prod.ext
    · have hComparison : (prodComparisonToTop A B (E.hom t)).1 =
          (Limits.prod.fst : A ⨯ B ⟶ A) (E.hom t) :=
        ConcreteCategory.congr_hom (prodComparisonToTop_fst A B) _
      have hProjection : (Limits.prod.fst : A ⨯ B ⟶ A) (E.hom t) =
          (CartesianMonoidalCategory.fst A B) t :=
        ConcreteCategory.congr_hom (tensorSelectedProductIso_hom_fst A B) t
      exact hComparison.trans (hProjection.trans (tensorMk_fst a b))
    · have hComparison : (prodComparisonToTop A B (E.hom t)).2 =
          (Limits.prod.snd : A ⨯ B ⟶ B) (E.hom t) :=
        ConcreteCategory.congr_hom (prodComparisonToTop_snd A B) _
      have hProjection : (Limits.prod.snd : A ⨯ B ⟶ B) (E.hom t) =
          (CartesianMonoidalCategory.snd A B) t :=
        ConcreteCategory.congr_hom (tensorSelectedProductIso_hom_snd A B) t
      exact hComparison.trans (hProjection.trans (tensorMk_snd a b))
  have hPoint : E.hom t = p :=
    (prodComparisonToTop_bijective A B).1
      (hPair.trans (prodComparisonToTop_prodPoint A B a b).symm)
  have hInv : T.inv p = t :=
    (congrArg E.inv hPoint).symm.trans (Iso.hom_inv_id_apply E t)
  have hConst : (TopCat.const t : TopCat.of PUnit.{u + 1} ⟶
      (A ⊗ B : CGWH.{u, u}).toTop) =
        (TopCat.const p : TopCat.of PUnit.{u + 1} ⟶ (A ⨯ B).toTop) ≫ T.inv := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    exact hInv.symm
  rw [hConst]
  let : (cofibrations TopCat.{u}).RespectsIso := by
    rw [← trivialFibrations_llp (C := TopCat.{u})]
    infer_instance
  exact (cofibration_iff _).mpr
    (MorphismProperty.RespectsIso.postcomp (cofibrations TopCat.{u})
      T.inv (TopCat.const p) hSource.mem)

/-- An original realized plus map with a commutative target fundamental
group derives a multiplication and BOTH whole point-relative unit
families on its actual native target. The original product map and
whole multiplication triangle are retained. -/
public theorem exists_hSpaceData_of_realized_plus
    (X Y : SSet.{u})
    [PathConnectedSpace (SSet.toCGWH.{u, u}.obj X)]
    [PathConnectedSpace (SSet.toCGWH.{u, u}.obj Y)]
    (x : X.obj (op ⦋0⦌)) (y : Y.obj (op ⦋0⦌))
    (q : SSet.toCGWH.{u, u}.obj X ⟶ SSet.toCGWH.{u, u}.obj Y)
    (hq : q (SSet.realizedVertex x) = SSet.realizedVertex y)
    (P : Subgroup (FundamentalGroup (SSet.toCGWH.{u, u}.obj X) (SSet.realizedVertex x)))
    [P.Normal] [Group.IsPerfect P]
    (hi : @TopCat.IsPlusConstructionAt (SSet.toCGWH.{u, u}.obj X).toTop
      (SSet.toCGWH.{u, u}.obj Y).toTop (cgwhToTop.map q)
      (SSet.realizedVertex x) (SSet.realizedVertex y) hq P ‹P.Normal› ‹Group.IsPerfect P›)
    [IsMulCommutative (FundamentalGroup (SSet.toCGWH.{u, u}.obj Y) (SSet.realizedVertex y))]
    (muA : (SSet.toCGWH.{u, u}.obj X) ⨯ (SSet.toCGWH.{u, u}.obj X) ⟶
      SSet.toCGWH.{u, u}.obj X)
    (hmuA : muA (tensorMk (SSet.realizedVertex x) (SSet.realizedVertex x)) =
      SSet.realizedVertex x)
    (hLeft : Nonempty (ContinuousMap.HomotopyRel (cgwhToTop.map q).hom
      (cgwhToTop.map (hspaceLeftUnitMap _ muA (SSet.realizedVertex x) ≫ q)).hom
        {SSet.realizedVertex x}))
    (hRight : Nonempty (ContinuousMap.HomotopyRel (cgwhToTop.map q).hom
      (cgwhToTop.map (hspaceRightUnitMap _ muA (SSet.realizedVertex x) ≫ q)).hom
        {SSet.realizedVertex x})) :
    ∃ H : HSpaceData (SSet.toCGWH.{u, u}.obj Y),
      H.e = SSet.realizedVertex y ∧
      Nonempty (ContinuousMap.HomotopyRel (cgwhToTop.map ((q ⊗ₘ q) ≫ H.mul)).hom
        (cgwhToTop.map (muA ≫ q)).hom
          {tensorMk (SSet.realizedVertex x) (SSet.realizedVertex x)}) := by
  let A := SSet.toCGWH.{u, u}.obj X
  let M := SSet.toCGWH.{u, u}.obj Y
  let a : A := SSet.realizedVertex x
  let m : M := SSet.realizedVertex y
  letI : Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A.toTop) :=
    SSet.realizedVertex_pointMap_cofibration X x
  letI : Cofibration (TopCat.const m : TopCat.of PUnit.{u + 1} ⟶ M.toTop) :=
    SSet.realizedVertex_pointMap_cofibration Y y
  letI : Cofibration (TopCat.const (tensorMk a a) :
      TopCat.of PUnit.{u + 1} ⟶ (A ⊗ A : CGWH.{u, u}).toTop) := by
    exact tensorPoint_cofibration A A a a (realizedProductPoint_cofibration X X x x)
  letI : Cofibration (TopCat.const (tensorMk m m) :
      TopCat.of PUnit.{u + 1} ⟶ (M ⊗ M : CGWH.{u, u}).toTop) := by
    exact tensorPoint_cofibration M M m m (realizedProductPoint_cofibration Y Y y y)
  letI : PathConnectedSpace (M ⊗ M : CGWH.{u, u}) := realizedProduct_pathConnected Y Y y y
  let Q := nativeProductPlusSubgroup A a P
  obtain ⟨hQN, hQP, hqq⟩ := nativeProduct_isPlus A M q a m hq P hi
  letI : Q.Normal := hQN
  letI : Group.IsPerfect Q := hQP
  let f0 : (A ⊗ A : CGWH.{u, u}).toTop ⟶ M.toTop := cgwhToTop.map (muA ≫ q)
  have hf0 : f0 (tensorMk a a) = m := (congrArg q hmuA).trans hq
  letI : IsMulCommutative (FundamentalGroup M.toTop m) :=
    (inferInstance : IsMulCommutative
      (FundamentalGroup (SSet.toCGWH.{u, u}.obj Y) (SSet.realizedVertex y)))
  let fm := FundamentalGroup.mapOfEq f0.hom hf0
  have hkill : ∀ p ∈ Q, FundamentalGroup.mapOfEq f0.hom rfl p = 1 := by
    intro p hp
    exact (FundamentalGroup.mapOfEq_eq_one_iff f0.hom hf0 p).mp
      (fm.eq_one_of_mem_perfect_subgroup Q hp)
  obtain ⟨F, hF, ⟨KF⟩, _⟩ := hqq.exists_point_relative_extension_of_cwType
    (TopCat.nativeSingularPointModelOfCofibrantPoint
      (A ⊗ A : CGWH.{u, u}).toTop (tensorMk a a)).cwType
    (TopCat.nativeSingularPointModelOfCofibrantPoint
      (M ⊗ M : CGWH.{u, u}).toTop (tensorMk m m)).cwType
    M.toTop f0 hkill
  let muM : M ⨯ M ⟶ M := ConcreteCategory.ofHom F.hom
  have hmuMap : cgwhToTop.map muM = F := by
    apply TopCat.hom_ext
    change ConcreteCategory.hom (C := CGWH.{u, u}) muM = F.hom
    exact ConcreteCategory.hom_ofHom _
  have hmuM : muM (tensorMk m m) = m :=
    (ConcreteCategory.congr_hom hmuMap (tensorMk m m)).trans (hF.trans hf0)
  let qTensor : (A ⊗ A : CGWH.{u, u}).toTop ⟶ (M ⊗ M : CGWH.{u, u}).toTop :=
    cgwhToTop.map (q ⊗ₘ q)
  let muTop : (M ⊗ M : CGWH.{u, u}).toTop ⟶ M.toTop := cgwhToTop.map muM
  let muComposite : (A ⊗ A : CGWH.{u, u}).toTop ⟶ M.toTop :=
    cgwhToTop.map ((q ⊗ₘ q) ≫ muM)
  have hmuTop : muTop = F := hmuMap
  have hComposite : muComposite = qTensor ≫ muTop := cgwhToTop.map_comp (q ⊗ₘ q) muM
  have hCompositeF : muComposite = qTensor ≫ F :=
    hComposite.trans (congrArg
      (fun g : (M ⊗ M : CGWH.{u, u}).toTop ⟶ M.toTop => qTensor ≫ g) hmuTop)
  have hKSource : (qTensor ≫ F).hom = muComposite.hom :=
    (congrArg TopCat.Hom.hom hCompositeF).symm
  let K : ContinuousMap.HomotopyRel (cgwhToTop.map ((q ⊗ₘ q) ≫ muM)).hom
      (cgwhToTop.map (muA ≫ q)).hom {tensorMk a a} :=
    KF.cast hKSource rfl
  let L := leftUnit_sourceTriangle q a m hq muA muM K hLeft.some
  let R := rightUnit_sourceTriangle q a m hq muA muM K hRight.some
  let qTop : A.toTop ⟶ M.toTop := cgwhToTop.map q
  have hqTop : qTop a = m := hq
  have hKernel :
      (FundamentalGroup.mapOfEq (x := a) (y := m) qTop.hom hqTop).ker = P :=
    @TopCat.IsPlusConstructionAt.kernel_eq A.toTop M.toTop qTop a m hqTop P
      ‹P.Normal› ‹Group.IsPerfect P› hi
  have hkillQ : ∀ p ∈ P, FundamentalGroup.mapOfEq (cgwhToTop.map q).hom rfl p = 1 := by
    intro p hp
    have hMem : p ∈
        (FundamentalGroup.mapOfEq (x := a) (y := m) qTop.hom hqTop).ker :=
      Eq.mp (congrArg (fun S : Subgroup (FundamentalGroup A.toTop a) => p ∈ S)
        hKernel.symm) hp
    have hk : FundamentalGroup.mapOfEq (x := a) (y := m) qTop.hom hqTop p = 1 :=
      MonoidHom.mem_ker.mp hMem
    exact (FundamentalGroup.mapOfEq_eq_one_iff
      (x := a) (y := m) qTop.hom hqTop p).mp hk
  obtain ⟨F0, _, _, hUnique⟩ := hi.exists_point_relative_extension_of_cwType
    (TopCat.nativeSingularPointModelOfCofibrantPoint A.toTop a).cwType
    (TopCat.nativeSingularPointModelOfCofibrantPoint M.toTop m).cwType
    M.toTop (cgwhToTop.map q) hkillQ
  have hId : Nonempty (ContinuousMap.HomotopyRel
      (cgwhToTop.map q ≫ (𝟙 M.toTop)).hom (cgwhToTop.map q).hom {a}) :=
    ⟨(ContinuousMap.HomotopyRel.refl (cgwhToTop.map q).hom {a}).cast
      (congrArg TopCat.Hom.hom (Category.comp_id (cgwhToTop.map q)).symm) rfl⟩
  obtain ⟨⟨FId⟩, _⟩ := hUnique (𝟙 M.toTop) hId
  obtain ⟨_, ⟨LF⟩⟩ := hUnique (cgwhToTop.map (hspaceLeftUnitMap M muM m)) ⟨L⟩
  obtain ⟨_, ⟨RF⟩⟩ := hUnique (cgwhToTop.map (hspaceRightUnitMap M muM m)) ⟨R⟩
  let H : HSpaceData M :=
    { mul := muM
      e := m
      mul_e_e := (congrArg muM (tensorMk_eq_prodPoint m m)).symm.trans hmuM
      left_unit := LF.trans (FId.cast rfl (TopCat.hom_id (X := M.toTop)))
      right_unit := RF.trans (FId.cast rfl (TopCat.hom_id (X := M.toTop))) }
  exact ⟨H, rfl, ⟨K⟩⟩

end CGWH

end
