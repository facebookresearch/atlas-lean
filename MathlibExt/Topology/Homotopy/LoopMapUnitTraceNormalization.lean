/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison
public import MathlibExt.Topology.Homotopy.PointTraceUnitContraction
public import MathlibExt.Topology.Homotopy.MiddleUnitTriangle

/-!
# The actual whole loop-map unit trace

The original chosen-root, middle and moving-tail unit traces telescope
through the same joint root-unit contraction. Every original family and
nested clock is retained, and all source and target casts are derived from
the actual mapped-unit and root-family values.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- The whole original loop-map unit path, including its chosen root
homotopy, compares with the same root contractions at its two original
weakly pointed endpoints. -/
theorem loopMapHomotopyOfMap_unitTrace_homotopic (f g : WeaklyPointed x y)
    (H : Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath)) :
    ((loopMapHomotopyOfMap f g H Hp).evalAt (Path.refl x)).Homotopic
      ((((rootUnitContraction (fun r : Path (f.hom x) y => r)
        continuous_eval).evalAt f.rootPath).trans
          ((rootUnitContraction (fun r : Path (g.hom x) y => r)
            continuous_eval).evalAt g.rootPath).symm).cast
              (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath)
              (loopMapUnit_eq_rootUnitLoopFamily g.hom g.rootPath)) := by
  let e : LoopSpace X x := Path.refl x
  let P : Path (f.hom x) (g.hom x) := H.evalAt x
  let q : Path (g.hom x) y := g.rootPath
  let c : Path (f.hom x) y := P.trans q
  let m : WeaklyPointed x y := ⟨f.hom, c⟩
  have ef : f.loopMap e = loopBasepointChange f.rootPath (Path.refl (f.hom x)) :=
    (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath).trans
      (rootUnitLoopFamily_pathSpace_apply f.rootPath)
  have ec : m.loopMap e = loopBasepointChange c (Path.refl (f.hom x)) :=
    (loopMapUnit_eq_rootUnitLoopFamily f.hom c).trans
      (rootUnitLoopFamily_pathSpace_apply c)
  have eg : g.loopMap e = loopBasepointChange q (Path.refl (g.hom x)) :=
    (loopMapUnit_eq_rootUnitLoopFamily g.hom q).trans
      (rootUnitLoopFamily_pathSpace_apply q)
  let A : Path (loopBasepointChange f.rootPath (Path.refl (f.hom x)))
      (loopBasepointChange c (Path.refl (f.hom x))) :=
    ((loopMapRootPathHomotopy f.hom Hp).evalAt e).cast ef.symm ec.symm
  let B : Path (loopBasepointChange c (Path.refl (f.hom x)))
      (loopBasepointChange q (loopBasepointChange P (Path.refl (f.hom x)))) :=
    (loopBasepointChangeTransHomotopy P q).evalAt (Path.refl (f.hom x))
  let C : Path (loopBasepointChange q (loopBasepointChange P (Path.refl (f.hom x))))
      (loopBasepointChange q (Path.refl (g.hom x))) :=
    ((((Homotopy.refl (loopBasepointChange q)).comp
      (Homotopy.traceConjugationLoopHomotopy H x)).evalAt e).cast
        (congrArg (loopBasepointChange q)
          (congrArg (loopBasepointChange P) (strictLoopMap_refl f.hom x))).symm
        (congrArg (loopBasepointChange q) (strictLoopMap_refl g.hom x)).symm)
  let Uf : Path (loopBasepointChange f.rootPath (Path.refl (f.hom x))) (Path.refl y) :=
    ((rootUnitContraction (fun r : Path (f.hom x) y => r)
      continuous_eval).evalAt f.rootPath).cast
        (rootUnitLoopFamily_pathSpace_apply f.rootPath).symm rfl
  let Uc : Path (loopBasepointChange c (Path.refl (f.hom x))) (Path.refl y) :=
    ((rootUnitContraction (fun r : Path (f.hom x) y => r)
      continuous_eval).evalAt c).cast
        (rootUnitLoopFamily_pathSpace_apply c).symm rfl
  let Up : Path (loopBasepointChange P (Path.refl (f.hom x))) (Path.refl (g.hom x)) :=
    ((rootUnitContraction (fun r : Path (f.hom x) (g.hom x) => r)
      continuous_eval).evalAt P).cast
        (rootUnitLoopFamily_pathSpace_apply P).symm rfl
  let Uq : Path (loopBasepointChange q (Path.refl (g.hom x))) (Path.refl y) :=
    ((rootUnitContraction (fun r : Path (g.hom x) y => r)
      continuous_eval).evalAt q).cast
        (rootUnitLoopFamily_pathSpace_apply q).symm rfl
  let V : Path (loopBasepointChange q (loopBasepointChange P (Path.refl (f.hom x))))
      (loopBasepointChange q (Path.refl (g.hom x))) :=
    Up.map (loopBasepointChange q).continuous
  have hA : A.Homotopic (Uf.trans Uc.symm) := by
    obtain ⟨K⟩ := loopMapRootPathHomotopy_unitTrace_homotopic f.hom Hp
    refine ⟨(K.pathCast ef.symm ec.symm).cast rfl ?_⟩
    apply Path.ext
    funext t
    rfl
  have hC : C.Homotopic V :=
    Homotopy.traceConjugationLoopHomotopy_postcomp_unitTrace_homotopic H x q
  have hBoundary : (B.trans (V.trans Uq)).Homotopic Uc :=
    loopBasepointChangeTransHomotopy_unitTriangle_homotopic P q
  have hBoundaryAssoc : ((B.trans V).trans Uq).Homotopic Uc :=
    (Path.Homotopic.trans_assoc B V Uq).trans hBoundary
  have hTailCancel : (((B.trans V).trans Uq).trans Uq.symm).Homotopic (B.trans V) :=
    (Path.Homotopic.trans_assoc (B.trans V) Uq Uq.symm).trans
      (((Path.Homotopic.refl (B.trans V)).hcomp (Path.Homotopic.trans_symm Uq)).trans
        (Path.Homotopic.trans_refl (B.trans V)))
  have hTail : (B.trans V).Homotopic (Uc.trans Uq.symm) :=
    hTailCancel.symm.trans (hBoundaryAssoc.hcomp (Path.Homotopic.refl Uq.symm))
  have hInner : (Uc.symm.trans (Uc.trans Uq.symm)).Homotopic Uq.symm :=
    (Path.Homotopic.trans_assoc Uc.symm Uc Uq.symm).symm.trans
      (((Path.Homotopic.symm_trans Uc).hcomp (Path.Homotopic.refl Uq.symm)).trans
        (Path.Homotopic.refl_trans Uq.symm))
  have hFinal : ((Uf.trans Uc.symm).trans (Uc.trans Uq.symm)).Homotopic
      (Uf.trans Uq.symm) :=
    (Path.Homotopic.trans_assoc Uf Uc.symm (Uc.trans Uq.symm)).trans
      ((Path.Homotopic.refl Uf).hcomp hInner)
  have hNormalizedPieces : (A.trans (B.trans C)).Homotopic (Uf.trans Uq.symm) :=
    (hA.hcomp ((Path.Homotopic.refl B).hcomp hC)).trans
      (((Path.Homotopic.refl (Uf.trans Uc.symm)).hcomp hTail).trans hFinal)
  have hPieces : (((loopMapHomotopyOfMap f g H Hp).evalAt e).cast
      ef.symm eg.symm) = A.trans (B.trans C) := by
    apply Path.ext
    funext t
    change loopMapHomotopyOfMap f g H Hp (t, e) = (A.trans (B.trans C)) t
    rw [loopMapHomotopyOfMap_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dite_eq_left ht]
      rfl
    · simp only [dite_eq_right ht]
      rw [Path.trans_apply]
      let r : I := ⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
      by_cases hr : 2 * (t : ℝ) - 1 ≤ 1 / 2
      · have hrTyped : (r : ℝ) ≤ 1 / 2 := hr
        simp only [dite_eq_left hr, ite_eq_left hr]
        let s : I := ⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg r, hrTyped⟩⟩
        exact congrArg (fun gamma : LoopSpace Y (f.hom x) =>
          loopBasepointChangeTransHomotopy P q (s, gamma)) (strictLoopMap_refl f.hom x)
      · simp only [dite_eq_right hr, ite_eq_right hr]
        rfl
  have hCore : (((loopMapHomotopyOfMap f g H Hp).evalAt e).cast
      ef.symm eg.symm).Homotopic (Uf.trans Uq.symm) := by
    obtain ⟨K⟩ := hNormalizedPieces
    exact ⟨K.cast hPieces.symm rfl⟩
  obtain ⟨K⟩ := hCore
  have hNativeSource :
      ((((loopMapHomotopyOfMap f g H Hp).evalAt e).cast ef.symm eg.symm).cast ef eg) =
        (loopMapHomotopyOfMap f g H Hp).evalAt e := by
    apply Path.ext
    funext t
    rfl
  have hNativeTarget : (Uf.trans Uq.symm).cast ef eg =
      ((((rootUnitContraction (fun r : Path (f.hom x) y => r)
        continuous_eval).evalAt f.rootPath).trans
          ((rootUnitContraction (fun r : Path (g.hom x) y => r)
            continuous_eval).evalAt g.rootPath).symm).cast
              (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath)
              (loopMapUnit_eq_rootUnitLoopFamily g.hom g.rootPath)) := by
    apply Path.ext
    funext t
    rfl
  exact ⟨(K.pathCast ef eg).cast hNativeSource hNativeTarget⟩

end ContinuousMap.WeaklyPointed

end
