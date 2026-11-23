/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HSpaceRelativePulledCoverComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverBaseMapComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverPointTransport

/-!
# The original pulled unit-total map and its homology isomorphism

Both coordinates of this map are the original mapping-path map and the
original induced native base-cover map. The three actual inclusion,
factorization and base-comparison maps recover this same whole map.
Ordinary integral homology of the arbitrary original continuous map
therefore gives homology isomorphism of this actual pulled unit-total map.
No cover-homology or expected comparison is a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace TopCat.HSpaceCommonUnitFibration

/-- The actual original unit-total map pulled along its actual base-cover map. -/
def originalPulledUnitMap {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    pullback (unitProjection X)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x))) ⟶
    pullback (unitProjection Y)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
        ((baseMap f).app (op ⦋0⦌)
          ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
            (TopCat.toSSetObj₀Equiv.symm x)))) := by
  let BX := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let BY := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y))
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let h := baseMap f
  let n := SSet.KanComplex.nativeCoverMap h b
  let px := unitProjection X
  let py := unitProjection Y
  let πx := SSet.KanComplex.nativeCoverProjection BX b
  let πy := SSet.KanComplex.nativeCoverProjection BY (h.app (op ⦋0⦌) b)
  let a := pullback.fst px πx
  let s := pullback.snd px πx
  let m := unitTotalMap f
  exact pullback.lift (a ≫ m) (s ≫ n) (by
    have hM : m ≫ py = px ≫ h := unitTotalMap_projection f
    have hN : n ≫ πy = πx ≫ h := SSet.KanComplex.nativeCoverMap_projection h b
    have hP : a ≫ px = s ≫ πx := pullback.condition
    exact (Category.assoc a m py).trans
      ((congrArg (fun k => a ≫ k) hM).trans
        ((Category.assoc a px h).symm.trans
          ((congrArg (fun k => k ≫ h) hP).trans
            ((Category.assoc s πx h).trans
              ((congrArg (fun k => s ≫ k) hN.symm).trans (Category.assoc s n πy).symm))))))

/-- Its original total-space coordinate is exactly the actual mapping-path map. -/
theorem originalPulledUnitMap_fst {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    originalPulledUnitMap f x ≫ pullback.fst (unitProjection Y)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
        ((baseMap f).app (op ⦋0⦌)
          ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
            (TopCat.toSSetObj₀Equiv.symm x)))) =
    pullback.fst (unitProjection X)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x))) ≫ unitTotalMap f := pullback.lift_fst _ _ _

/-- Its complete cover coordinate is the SAME original induced native map. -/
theorem originalPulledUnitMap_snd {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    originalPulledUnitMap f x ≫ pullback.snd (unitProjection Y)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
        ((baseMap f).app (op ⦋0⦌)
          ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
            (TopCat.toSSetObj₀Equiv.symm x)))) =
    pullback.snd (unitProjection X)
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X)))
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x))) ≫
      SSet.KanComplex.nativeCoverMap (baseMap f)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) := pullback.lift_snd _ _ _

/-- The actual three comparison maps recover this SAME original map, with both coordinates. -/
theorem originalPulledUnitMap_factor {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    SSet.KanComplex.nativeCoverBaseChangeMap (relativeInclusion f)
        (relativeInclusion_projection f)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) ≫
      SSet.KanComplex.nativeCoverBaseChangeMap (relativeComparison f) (relativeProjection_eq f).symm
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) ≫
      SSet.KanComplex.nativeCoverPullbackBaseMap (baseMap f) (unitProjection Y)
        ((SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
          (TopCat.toSSetObj₀Equiv.symm x)) = originalPulledUnitMap f x := by
  let B := CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj X))
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let u := relativeInclusion f
  let r := relativeComparison f
  let h := baseMap f
  let py := unitProjection Y
  let px := unitProjection X
  let pm := relativeProjection f
  let pq := pullback.fst h py
  let π := SSet.KanComplex.nativeCoverProjection B b
  let cI := SSet.KanComplex.nativeCoverBaseChangeMap u (relativeInclusion_projection f) b
  let cR := SSet.KanComplex.nativeCoverBaseChangeMap r (relativeProjection_eq f).symm b
  let cB := SSet.KanComplex.nativeCoverPullbackBaseMap h py b
  let fi := pullback.fst px π
  let fm := pullback.fst pm π
  let fq := pullback.fst pq π
  let si := pullback.snd px π
  let sm := pullback.snd pm π
  let sq := pullback.snd pq π
  let j := pullback.snd h py
  have hI : cI ≫ fm = fi ≫ u := SSet.KanComplex.nativeCoverBaseChangeMap_fst _ _ _
  have hR : cR ≫ fq = fm ≫ r := SSet.KanComplex.nativeCoverBaseChangeMap_fst _ _ _
  have hSnd : commonTotalMap f ≫ j = unitTotalMap f := by
    change commonTotalMap f ≫ pullback.snd (baseMap f) (unitProjection Y) = _
    rw [← commonTargetComparison_eq f]
    exact commonTotalMap_snd f
  have hReturn : u ≫ (r ≫ j) = unitTotalMap f :=
    (Category.assoc u r j).symm.trans
      ((congrArg (fun k => k ≫ j) (relativeInclusion_comparison f)).trans hSnd)
  apply pullback.hom_ext
  · let fy := pullback.fst py
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
        (h.app (op ⦋0⦌) b))
    have hB : cB ≫ fy = fq ≫ j := SSet.KanComplex.nativeCoverPullbackBaseMap_fst h py b
    have hT : (cI ≫ cR ≫ cB) ≫ fy = fi ≫ (u ≫ (r ≫ j)) :=
      (Category.assoc cI (cR ≫ cB) fy).trans
        ((congrArg (fun k => cI ≫ k) (Category.assoc cR cB fy)).trans
          ((congrArg (fun k => cI ≫ (cR ≫ k)) hB).trans
            ((congrArg (fun k => cI ≫ k) (Category.assoc cR fq j).symm).trans
              ((congrArg (fun k => cI ≫ (k ≫ j)) hR).trans
                ((congrArg (fun k => cI ≫ k) (Category.assoc fm r j)).trans
                  ((Category.assoc cI fm (r ≫ j)).symm.trans
                    ((congrArg (fun k => k ≫ (r ≫ j)) hI).trans (Category.assoc fi u (r ≫ j)))))))))
    exact hT.trans
      ((congrArg (fun k => fi ≫ k) hReturn).trans (originalPulledUnitMap_fst f x).symm)
  · let sy := pullback.snd py
      (SSet.KanComplex.nativeCoverProjection
        (CategoryTheory.nerve (SSet.FundamentalGroupoid (TopCat.toSSet.obj Y)))
        (h.app (op ⦋0⦌) b))
    let nh := SSet.KanComplex.nativeCoverMap h b
    have hB : cB ≫ sy = sq ≫ nh := SSet.KanComplex.nativeCoverPullbackBaseMap_snd h py b
    have hRS : cR ≫ sq = sm := SSet.KanComplex.nativeCoverBaseChangeMap_snd _ _ _
    have hIS : cI ≫ sm = si := SSet.KanComplex.nativeCoverBaseChangeMap_snd _ _ _
    have hT : (cI ≫ cR ≫ cB) ≫ sy = si ≫ nh :=
      (Category.assoc cI (cR ≫ cB) sy).trans
        ((congrArg (fun k => cI ≫ k) (Category.assoc cR cB sy)).trans
          ((congrArg (fun k => cI ≫ (cR ≫ k)) hB).trans
            ((congrArg (fun k => cI ≫ k) (Category.assoc cR sq nh).symm).trans
              ((congrArg (fun k => cI ≫ (k ≫ nh)) hRS).trans
                ((Category.assoc cI sm nh).symm.trans (congrArg (fun k => k ≫ nh) hIS))))))
    exact hT.trans (originalPulledUnitMap_snd f x).symm

private theorem homologyMap_isIso_of_weak {A B : SSet.{u}} (m : A ⟶ B)
    (hm : SSet.realizationWeakEquivalences m) (R : AddCommGrpCat.{u}) (n : ℕ) :
    IsIso (SSet.homologyMap m R n) := by
  let : QuasiIso (SSet.chainComplexMap m R) := hm.quasiIso_chainComplexMap_addCommGrp R
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap (SSet.chainComplexMap m R) n).mp
    (inferInstance : QuasiIsoAt (SSet.chainComplexMap m R) n)

/-- Ordinary Hiso of arbitrary original f gives Hiso of its actual pulled unit-total map. -/
theorem originalPulledUnitMap_integralHomology_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f))
    (x : X) (n : ℕ) :
    IsIso (SSet.homologyMap (originalPulledUnitMap f x)
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) n) := by
  let R : AddCommGrpCat.{u} := AlgebraicTopology.singularIntegralCoefficients
  let H := SSet.homologyFunctor R n
  let b := (SSet.KanComplex.nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
    (TopCat.toSSetObj₀Equiv.symm x)
  let cI := SSet.KanComplex.nativeCoverBaseChangeMap (relativeInclusion f)
    (relativeInclusion_projection f) b
  let cR := SSet.KanComplex.nativeCoverBaseChangeMap (relativeComparison f)
    (relativeProjection_eq f).symm b
  let cB := SSet.KanComplex.nativeCoverPullbackBaseMap (baseMap f) (unitProjection Y) b
  let : Fibration (unitProjection Y) := unitProjection_isFibration Y
  have hCmp := SSet.KanComplex.nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
    (relativeComparison f) (relativeProjection_eq f).symm b
      (relativeComparison_mem_realizationWeakEquivalences f)
  have hRaw : SSet.realizationWeakEquivalences
      (CategoryTheory.nerveMap (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f))) :=
    TopCat.HSpaceHomologyOne.nerveBaseMap_mem_realizationWeakEquivalences_of_integralHomologyOne_isIso
      f (hf 1)
  have hBase : SSet.realizationWeakEquivalences (baseMap f) := (baseMap_eq f).symm ▸ hRaw
  have hB := SSet.KanComplex.nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences
    (baseMap f) (unitProjection Y) b hBase
  let : IsIso (H.map cI) := originalPulledInclusion_integralHomology_isIso f hf x n
  let : IsIso (H.map cR) := homologyMap_isIso_of_weak cR hCmp R n
  let : IsIso (H.map cB) := homologyMap_isIso_of_weak cB hB R n
  have hFactor : H.map (cI ≫ cR ≫ cB) = H.map cI ≫ H.map cR ≫ H.map cB :=
    (H.map_comp cI (cR ≫ cB)).trans
      (congrArg (fun k => H.map cI ≫ k) (H.map_comp cR cB))
  have hMap : H.map (originalPulledUnitMap f x) = H.map cI ≫ H.map cR ≫ H.map cB :=
    (congrArg H.map (originalPulledUnitMap_factor f x)).symm.trans hFactor
  have hComposite : IsIso (H.map cI ≫ H.map cR ≫ H.map cB) :=
    IsIso.comp_isIso' (inferInstance : IsIso (H.map cI))
      (IsIso.comp_isIso' (inferInstance : IsIso (H.map cR))
        (inferInstance : IsIso (H.map cB)))
  change IsIso (H.map (originalPulledUnitMap f x))
  exact hMap.symm ▸ hComposite

end TopCat.HSpaceCommonUnitFibration
