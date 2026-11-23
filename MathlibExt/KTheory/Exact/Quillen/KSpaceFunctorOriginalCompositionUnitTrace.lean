/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorOriginalComposition
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFrameCompositionUnitTrace
public import MathlibExt.KTheory.Exact.Quillen.KSpaceFunctorAllKiMap

/-!
# The retained original composition trace and its designated units

The actual whole composition homotopy has the two original half clocks.
Its actual trace telescopes through the original composite root contraction
and the SAME201 component units. Both original component maps and root
families are retained. No root/coherence outcome is a caller hypothesis.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject ContinuousMap

universe uC vC uD vD uE vE

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

private theorem sixRoleCompositionUnitTraceComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    let UF := ((ContinuousMap.rootUnitContraction
      (fun p : Path ((NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C))
        (NQReal.basepoint D) => p) continuous_eval).evalAt
          (NQRealFunctorWeaklyPointed F).rootPath).cast
            (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F) rfl
    let UG := ((ContinuousMap.rootUnitContraction
      (fun p : Path ((NQRealFunctorWeaklyPointed G).hom (NQReal.basepoint D))
        (NQReal.basepoint E) => p) continuous_eval).evalAt
          (NQRealFunctorWeaklyPointed G).rootPath).cast
            (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily G) rfl
    let UFG := ((ContinuousMap.rootUnitContraction
      (fun p : Path ((NQRealFunctorWeaklyPointed (F ⋙ G)).hom (NQReal.basepoint C))
        (NQReal.basepoint E) => p) continuous_eval).evalAt
          (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath).cast
            (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily (F ⋙ G)) rfl
    (NQKSpaceFunctorOriginalCompUnitPath F G).Homotopic
      (UFG.trans ((UF.map (NQKSpaceFunctorMap G).continuous).trans UG).symm) := by
  let x := NQReal.basepoint C
  let y := NQReal.basepoint D
  let z := NQReal.basepoint E
  let eC : NQKSpace C := Path.refl x
  let f := NQRealFunctorWeaklyPointed F
  let g := NQRealFunctorWeaklyPointed G
  let a := NQRealFunctorWeaklyPointed (F ⋙ G)
  let b := ContinuousMap.WeaklyPointed.comp f g
  let p := f.rootPath.map g.hom.continuous
  let q : Path (a.hom x) z :=
    (p.cast (NQRealFunctor_comp_basepoint_eq F G) rfl).trans g.rootPath
  let w : ContinuousMap.WeaklyPointed x z := ⟨a.hom, q⟩
  let UA := (ContinuousMap.rootUnitContraction
    (fun r : Path (a.hom x) z => r) continuous_eval).evalAt a.rootPath
  let UQ := (ContinuousMap.rootUnitContraction
    (fun r : Path (a.hom x) z => r) continuous_eval).evalAt q
  let UBRaw := (ContinuousMap.rootUnitContraction
    (fun r : Path (b.hom x) z => r) continuous_eval).evalAt b.rootPath
  let UB : Path (b.loopMap eC) (Path.refl z) := UBRaw.cast
    (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily b.hom b.rootPath) rfl
  let UFW := ((ContinuousMap.rootUnitContraction
    (fun r : Path (f.hom x) y => r) continuous_eval).evalAt f.rootPath).cast
      (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath) rfl
  let UGW := ((ContinuousMap.rootUnitContraction
    (fun r : Path (g.hom y) z => r) continuous_eval).evalAt g.rootPath).cast
      (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily g.hom g.rootPath) rfl
  let UF := ((ContinuousMap.rootUnitContraction
    (fun r : Path (f.hom x) y => r) continuous_eval).evalAt f.rootPath).cast
      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily F) rfl
  let UG := ((ContinuousMap.rootUnitContraction
    (fun r : Path (g.hom y) z => r) continuous_eval).evalAt g.rootPath).cast
      (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily G) rfl
  let UFG : Path (NQKSpaceFunctorMap (F ⋙ G) eC) (Path.refl z) := UA.cast
    (NQKSpaceFunctorMap_unit_eq_rootUnitLoopFamily (F ⋙ G)) rfl
  let SW := (UFW.map g.loopMap.continuous).trans UGW
  let SN := (UF.map (NQKSpaceFunctorMap G).continuous).trans UG
  have hUQ (t : unitInterval) : UQ.toContinuousMap.toFun t = UBRaw.toContinuousMap.toFun t :=
    NQRealFunctorCompRootUnit_apply_eq F G t
  have hJoin : w.loopMap eC = b.loopMap eC :=
    (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily a.hom q).trans
      (UQ.source.symm.trans ((hUQ 0).trans
        (UBRaw.source.trans
          (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily
            b.hom b.rootPath).symm)))
  have hA : NQKSpaceFunctorMap (F ⋙ G) eC = a.loopMap eC :=
    (NQKSpaceFunctorMap_apply (F ⋙ G) eC).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply a eC).symm
  have hF : NQKSpaceFunctorMap F eC = f.loopMap eC :=
    (NQKSpaceFunctorMap_apply F eC).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply f eC).symm
  have hMapG : NQKSpaceFunctorMap G = g.loopMap := by
    apply ContinuousMap.ext
    intro gamma
    exact (NQKSpaceFunctorMap_apply G gamma).trans
      (ContinuousMap.WeaklyPointed.loopMap_apply g gamma).symm
  have hTarget : NQKSpaceFunctorMap G (NQKSpaceFunctorMap F eC) =
      g.loopMap (f.loopMap eC) :=
    (congrArg (fun K : C(NQKSpace D, NQKSpace E) => K (NQKSpaceFunctorMap F eC))
      hMapG).trans (congrArg g.loopMap hF)
  let P1 : Path (NQKSpaceFunctorMap (F ⋙ G) eC) (b.loopMap eC) :=
    ((ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom
      (NQRealFunctorCompMappedRootHomotopy F G)).evalAt eC).cast hA hJoin.symm
  let P2 : Path (b.loopMap eC) (NQKSpaceFunctorMap G (NQKSpaceFunctorMap F eC)) :=
    ((ContinuousMap.WeaklyPointed.loopMapCompHomotopy f g).evalAt eC).cast rfl hTarget
  have hFirstTarget :
      (((UA.trans UQ.symm).cast
        (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily a.hom a.rootPath)
        (ContinuousMap.WeaklyPointed.loopMapUnit_eq_rootUnitLoopFamily a.hom q)).cast
          hA hJoin.symm) = UFG.trans UB.symm := by
    apply Path.ext
    funext t
    change (UA.trans UQ.symm).toContinuousMap.toFun t =
      (UFG.trans UB.symm).toContinuousMap.toFun t
    have hL := Path.trans_apply UA UQ.symm t
    have hR := Path.trans_apply UFG UB.symm t
    have hv :
        (if ht : (t : ℝ) ≤ 1 / 2 then UA.toContinuousMap.toFun
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩
        else UQ.symm.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) =
        (if ht : (t : ℝ) ≤ 1 / 2 then UFG.toContinuousMap.toFun
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩
        else UB.symm.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) := by
      apply congrArg₂ (dite ((t : ℝ) ≤ 1 / 2))
      · funext ht
        have hCastValue (s : unitInterval) : UA.toContinuousMap.toFun s =
            UFG.toContinuousMap.toFun s := rfl
        exact hCastValue _
      · funext ht
        let r : unitInterval := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
        have hCastValue (s : unitInterval) : UBRaw.toContinuousMap.toFun s =
            UB.toContinuousMap.toFun s := rfl
        change UQ.toContinuousMap.toFun (unitInterval.symm r) =
          UB.toContinuousMap.toFun (unitInterval.symm r)
        exact (hUQ (unitInterval.symm r)).trans (hCastValue (unitInterval.symm r))
    exact hL.trans (hv.trans hR.symm)
  have hFirst : P1.Homotopic (UFG.trans UB.symm) := by
    obtain ⟨K⟩ := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy_unitTrace_homotopic
      a.hom (NQRealFunctorCompMappedRootHomotopy F G)
    exact ⟨(K.pathCast hA hJoin.symm).cast rfl hFirstTarget⟩
  have hTotalValue (t : unitInterval) : SW.toContinuousMap.toFun t = SN.toContinuousMap.toFun t :=
      by
    have hL := Path.trans_apply (UFW.map g.loopMap.continuous) UGW t
    have hR := Path.trans_apply (UF.map (NQKSpaceFunctorMap G).continuous) UG t
    have hv :
        (if ht : (t : ℝ) ≤ 1 / 2 then
          (UFW.map g.loopMap.continuous).toContinuousMap.toFun
            ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩
        else UGW.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) =
        (if ht : (t : ℝ) ≤ 1 / 2 then
          (UF.map (NQKSpaceFunctorMap G).continuous).toContinuousMap.toFun
            ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩
        else UG.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) := by
      apply congrArg₂ (dite ((t : ℝ) ≤ 1 / 2))
      · funext ht
        let r : unitInterval := ⟨2 * (t : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg t, ht⟩⟩
        have hCastValue : UFW.toContinuousMap.toFun r = UF.toContinuousMap.toFun r := rfl
        change g.loopMap (UFW.toContinuousMap.toFun r) =
          NQKSpaceFunctorMap G (UF.toContinuousMap.toFun r)
        exact (congrArg g.loopMap hCastValue).trans
          (congrArg (fun K : C(NQKSpace D, NQKSpace E) =>
            K (UF.toContinuousMap.toFun r)) hMapG).symm
      · funext ht
        have hCastValue (s : unitInterval) : UGW.toContinuousMap.toFun s =
            UG.toContinuousMap.toFun s := rfl
        exact hCastValue _
    exact hL.trans (hv.trans hR.symm)
  have hSecondTarget : (UB.trans SW.symm).cast rfl hTarget = UB.trans SN.symm := by
    apply Path.ext
    funext t
    change (UB.trans SW.symm).toContinuousMap.toFun t =
      (UB.trans SN.symm).toContinuousMap.toFun t
    have hL := Path.trans_apply UB SW.symm t
    have hR := Path.trans_apply UB SN.symm t
    have hv :
        (if ht : (t : ℝ) ≤ 1 / 2 then UB.toContinuousMap.toFun
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩
        else SW.symm.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) =
        (if ht : (t : ℝ) ≤ 1 / 2 then UB.toContinuousMap.toFun
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩
        else SN.symm.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) := by
      apply congrArg₂ (dite ((t : ℝ) ≤ 1 / 2))
      · funext ht
        rfl
      · funext ht
        let r : unitInterval := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
        change SW.toContinuousMap.toFun (unitInterval.symm r) =
          SN.toContinuousMap.toFun (unitInterval.symm r)
        exact hTotalValue (unitInterval.symm r)
    exact hL.trans (hv.trans hR.symm)
  have hSecond : P2.Homotopic (UB.trans SN.symm) := by
    obtain ⟨K⟩ := ContinuousMap.WeaklyPointed.loopMapCompHomotopy_unitTrace_homotopic f g
    exact ⟨(K.pathCast rfl hTarget).cast rfl hSecondTarget⟩
  let Cpath := NQKSpaceFunctorOriginalCompUnitPath F G
  have hActual : Cpath = P1.trans P2 := by
    apply Path.ext
    funext t
    have hUnit : Cpath.toContinuousMap.toFun t =
        (NQKSpaceFunctorOriginalCompHomotopy F G).toContinuousMap.toFun (t, eC) := by
      apply Path.ext
      funext s
      exact NQKSpaceFunctorOriginalCompUnitPath_apply F G t s
    have hWhole := NQKSpaceFunctorOriginalCompHomotopy_loopMap_value F G t eC
    have hP := Path.trans_apply P1 P2 t
    have hv :
        (if ht : (t : ℝ) ≤ 1 / 2 then
          (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom
            (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun
              (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
                ⟨unitInterval.nonneg t, ht⟩⟩, eC)
        else (ContinuousMap.WeaklyPointed.loopMapCompHomotopy f g).toContinuousMap.toFun
          (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, eC)) =
        (if ht : (t : ℝ) ≤ 1 / 2 then P1.toContinuousMap.toFun
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩
        else P2.toContinuousMap.toFun
          ⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩) := by
      apply congrArg₂ (dite ((t : ℝ) ≤ 1 / 2))
      · funext ht
        have hCastValue (s : unitInterval) :
            (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy a.hom
              (NQRealFunctorCompMappedRootHomotopy F G)).toContinuousMap.toFun (s, eC) =
                P1.toContinuousMap.toFun s := rfl
        exact hCastValue _
      · funext ht
        have hCastValue (s : unitInterval) :
            (ContinuousMap.WeaklyPointed.loopMapCompHomotopy f g).toContinuousMap.toFun (s, eC) =
                P2.toContinuousMap.toFun s := rfl
        exact hCastValue _
    exact hUnit.trans (hWhole.trans (hv.trans hP.symm))
  have hCancel : (UB.symm.trans (UB.trans SN.symm)).Homotopic SN.symm :=
    (Path.Homotopic.trans_assoc UB.symm UB SN.symm).symm.trans
      (((Path.Homotopic.symm_trans UB).hcomp (Path.Homotopic.refl SN.symm)).trans
        (Path.Homotopic.refl_trans SN.symm))
  have hFinal : ((UFG.trans UB.symm).trans (UB.trans SN.symm)).Homotopic
      (UFG.trans SN.symm) :=
    (Path.Homotopic.trans_assoc UFG UB.symm (UB.trans SN.symm)).trans
      ((Path.Homotopic.refl UFG).hcomp hCancel)
  obtain ⟨K⟩ := (hFirst.hcomp hSecond).trans hFinal
  exact ⟨K.cast hActual.symm rfl⟩


/-- The ACTUAL whole composition trace compares with the SAME201 direct unit
followed by the reverse of the mapped first unit and original second unit.
All SIX category Obj/Hom roles remain independent. -/
theorem NQKSpaceFunctorOriginalCompUnitPath_homotopic_rootUnits
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (NQKSpaceFunctorOriginalCompUnitPath F G).Homotopic
      ((NQKSpaceFunctorKiUnitRootPath (F ⋙ G)).trans
        (((NQKSpaceFunctorKiUnitRootPath F).map (NQKSpaceFunctorMap G).continuous).trans
          (NQKSpaceFunctorKiUnitRootPath G)).symm) := by
  rw [NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction (F ⋙ G),
    NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction F,
        NQKSpaceFunctorKiUnitRootPath_eq_rootUnitContraction G]
  exact sixRoleCompositionUnitTraceComputed F G

/-- The exact original rooted compatibility needed by ALL positive Ki
composition is derived from the actual whole family and original unit triangles.
No rooted/homotopy/coherence outcome is supplied by the caller. -/
theorem NQKSpaceFunctorOriginalCompHomotopy_rooted_units
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (((NQKSpaceFunctorOriginalCompHomotopy F G).evalAt (Path.refl (NQReal.basepoint C))).trans
      (((NQKSpaceFunctorKiUnitRootPath F).map (NQKSpaceFunctorMap G).continuous).trans
        (NQKSpaceFunctorKiUnitRootPath G))).Homotopic
      (NQKSpaceFunctorKiUnitRootPath (F ⋙ G)) := by
  let U := NQKSpaceFunctorKiUnitRootPath (F ⋙ G)
  let S := ((NQKSpaceFunctorKiUnitRootPath F).map (NQKSpaceFunctorMap G).continuous).trans
    (NQKSpaceFunctorKiUnitRootPath G)
  have hTrace : (NQKSpaceFunctorOriginalCompUnitPath F G).Homotopic (U.trans S.symm) :=
    NQKSpaceFunctorOriginalCompUnitPath_homotopic_rootUnits F G
  have hRoot := (hTrace.hcomp (Path.Homotopic.refl S)).trans
    ((Path.Homotopic.trans_assoc U S.symm S).trans
      (((Path.Homotopic.refl U).hcomp (Path.Homotopic.symm_trans S)).trans
        (Path.Homotopic.trans_refl U)))
  have hActual : NQKSpaceFunctorOriginalCompUnitPath F G =
      (NQKSpaceFunctorOriginalCompHomotopy F G).evalAt (Path.refl (NQReal.basepoint C)) := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact NQKSpaceFunctorOriginalCompUnitPath_apply F G t s
  obtain ⟨K⟩ := hRoot
  exact ⟨K.cast (congrArg (fun P => P.trans S) hActual) rfl⟩

private theorem originalCompositionReverseRootUnitsComputed
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (((NQKSpaceFunctorOriginalCompHomotopy F G).symm.evalAt
      (Path.refl (NQReal.basepoint C))).trans
        (NQKSpaceFunctorKiUnitRootPath (F ⋙ G))).Homotopic
      (((NQKSpaceFunctorKiUnitRootPath F).map
        (NQKSpaceFunctorMap G).continuous).trans
          (NQKSpaceFunctorKiUnitRootPath G)) := by
  let x : NQKSpace C := Path.refl (NQReal.basepoint C)
  let H := NQKSpaceFunctorOriginalCompHomotopy F G
  let T := H.evalAt x
  let U := NQKSpaceFunctorKiUnitRootPath (F ⋙ G)
  let S := ((NQKSpaceFunctorKiUnitRootPath F).map
    (NQKSpaceFunctorMap G).continuous).trans (NQKSpaceFunctorKiUnitRootPath G)
  have hRoot : (T.trans S).Homotopic U :=
    NQKSpaceFunctorOriginalCompHomotopy_rooted_units F G
  have hReverse : (T.symm.trans U).Homotopic S :=
    ((Path.Homotopic.refl T.symm).hcomp hRoot.symm).trans
      ((Path.Homotopic.trans_assoc T.symm T S).symm.trans
        (((Path.Homotopic.symm_trans T).hcomp (Path.Homotopic.refl S)).trans
          (Path.Homotopic.refl_trans S)))
  have hTrace : H.symm.evalAt x = T.symm := by
    apply Path.ext
    funext t
    rfl
  obtain ⟨K⟩ := hReverse
  exact ⟨K.cast (congrArg
    (fun P : Path
      (NQKSpaceFunctorMap G (NQKSpaceFunctorMap F x))
      (NQKSpaceFunctorMap (F ⋙ G) x) => P.trans U) hTrace).symm rfl⟩

/-- The reverse of the same whole original composition family retains its
actual direct unit and both original component units. This is the orientation
used before the actual P/J retraction and split-sum comparisons. -/
theorem NQKSpaceFunctorOriginalCompHomotopy_reverse_rooted_units
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    (((NQKSpaceFunctorOriginalCompHomotopy F G).symm.evalAt
      (Path.refl (NQReal.basepoint C))).trans
        (NQKSpaceFunctorKiUnitRootPath (F ⋙ G))).Homotopic
      (((NQKSpaceFunctorKiUnitRootPath F).map
        (NQKSpaceFunctorMap G).continuous).trans
          (NQKSpaceFunctorKiUnitRootPath G)) :=
  originalCompositionReverseRootUnitsComputed F G

end AlgebraicKTheory

end
