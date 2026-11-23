/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison
public import MathlibExt.Topology.Homotopy.MiddleUnitTriangle

/-!
# The original loop-map composition unit trace

The actual middle trace of weakly pointed composition compares with the
same composite-root contraction and mapped component contractions. All
original endpoint casts, maps and root choices are retained.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v w

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- The actual original composition unit trace compares with the same
composite-root unit contraction and both original mapped component units. -/
theorem loopMapCompHomotopy_unitTrace_homotopic
    (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    let Uf := ((rootUnitContraction (fun p : Path (f.hom x) y => p)
      continuous_eval).evalAt f.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath) rfl
    let Ug := ((rootUnitContraction (fun p : Path (g.hom y) z => p)
      continuous_eval).evalAt g.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily g.hom g.rootPath) rfl
    let m := comp f g
    let Um := ((rootUnitContraction (fun p : Path (m.hom x) z => p)
      continuous_eval).evalAt m.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily m.hom m.rootPath) rfl
    ((loopMapCompHomotopy f g).evalAt (Path.refl x)).Homotopic
      (Um.trans ((Uf.map g.loopMap.continuous).trans Ug).symm) := by
  let ex : LoopSpace X x := Path.refl x
  let m := comp f g
  let p : Path (g.hom (f.hom x)) (g.hom y) := f.rootPath.map g.hom.continuous
  let q : Path (g.hom y) z := g.rootPath
  let Uf : Path (f.loopMap ex) (Path.refl y) :=
    ((rootUnitContraction (fun r : Path (f.hom x) y => r)
      continuous_eval).evalAt f.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath) rfl
  let Ug : Path (g.loopMap (Path.refl y)) (Path.refl z) :=
    ((rootUnitContraction (fun r : Path (g.hom y) z => r)
      continuous_eval).evalAt q).cast
        (loopMapUnit_eq_rootUnitLoopFamily g.hom q) rfl
  let Um : Path (m.loopMap ex) (Path.refl z) :=
    ((rootUnitContraction (fun r : Path (m.hom x) z => r)
      continuous_eval).evalAt m.rootPath).cast
        (loopMapUnit_eq_rootUnitLoopFamily m.hom m.rootPath) rfl
  let Up : Path (loopBasepointChange p (Path.refl (g.hom (f.hom x))))
      (Path.refl (g.hom y)) :=
    ((rootUnitContraction (fun r : Path (g.hom (f.hom x)) (g.hom y) => r)
      continuous_eval).evalAt p).cast
        (rootUnitLoopFamily_pathSpace_apply p).symm rfl
  let Uq : Path (loopBasepointChange q (Path.refl (g.hom y))) (Path.refl z) :=
    ((rootUnitContraction (fun r : Path (g.hom y) z => r)
      continuous_eval).evalAt q).cast
        (rootUnitLoopFamily_pathSpace_apply q).symm rfl
  let Uc : Path (loopBasepointChange (p.trans q) (Path.refl (g.hom (f.hom x))))
      (Path.refl z) :=
    ((rootUnitContraction (fun r : Path (g.hom (f.hom x)) z => r)
      continuous_eval).evalAt (p.trans q)).cast
        (rootUnitLoopFamily_pathSpace_apply (p.trans q)).symm rfl
  let V := Up.map (loopBasepointChange q).continuous
  let S := Uf.map g.loopMap.continuous
  let T := (loopBasepointChangeTransHomotopy p q).evalAt
    (Path.refl (g.hom (f.hom x)))
  let C := (loopMapCompHomotopy f g).evalAt ex
  have hMappedValue (t : I) : S.toContinuousMap.toFun t = V.toContinuousMap.toFun t := by
    have hFactor : g.loopMap (Uf.toContinuousMap.toFun t) =
        loopBasepointChange q ((Uf.toContinuousMap.toFun t).map g.hom.continuous) :=
      (congrArg (fun K : C(LoopSpace Y y, LoopSpace Z z) =>
        K (Uf.toContinuousMap.toFun t))
          (loopMap_eq_loopBasepointChange_comp_strictLoopMap g)).trans
            (congrArg (loopBasepointChange q)
              (strictLoopMap_apply g.hom y (Uf.toContinuousMap.toFun t)))
    have hUnit : (Uf.toContinuousMap.toFun t).map g.hom.continuous =
        Up.toContinuousMap.toFun t := by
      change (rootUnitContraction (fun r : Path (f.hom x) y => r)
          continuous_eval (t, f.rootPath)).map g.hom.continuous =
        rootUnitContraction (fun r : Path (g.hom (f.hom x)) (g.hom y) => r)
          continuous_eval (t, p)
      have hTransport := rootUnitContraction_mappedPath_cast g.hom f.rootPath rfl rfl t
      simpa only [Path.cast_rfl_rfl] using hTransport
    exact hFactor.trans (congrArg (loopBasepointChange q) hUnit)
  have etaV : g.loopMap (f.loopMap ex) =
      loopBasepointChange q (loopBasepointChange p (Path.refl (g.hom (f.hom x)))) :=
    S.source.symm.trans ((hMappedValue 0).trans V.source)
  have etaG : g.loopMap (Path.refl y) = loopBasepointChange q (Path.refl (g.hom y)) :=
    (loopMapUnit_eq_rootUnitLoopFamily g.hom q).trans
      (rootUnitLoopFamily_pathSpace_apply q)
  have etaM : m.loopMap ex =
      loopBasepointChange (p.trans q) (Path.refl (g.hom (f.hom x))) :=
    (loopMapUnit_eq_rootUnitLoopFamily m.hom m.rootPath).trans
      (rootUnitLoopFamily_pathSpace_apply m.rootPath)
  have hS : V.cast etaV etaG = S := by
    apply Path.ext
    funext t
    exact (hMappedValue t).symm
  have hUg : Uq.cast etaG rfl = Ug := by
    apply Path.ext
    funext t
    rfl
  have hUm : Uc.cast etaM rfl = Um := by
    apply Path.ext
    funext t
    rfl
  have hC : T.cast etaM etaV = C := by
    apply Path.ext
    funext t
    change loopBasepointChangeTransHomotopy p q
        (t, Path.refl (g.hom (f.hom x))) = loopMapCompHomotopy f g (t, ex)
    exact ((loopMapCompHomotopy_apply f g t ex).trans
      (congrArg (fun gamma : LoopSpace Z (g.hom (f.hom x)) =>
        loopBasepointChangeTransHomotopy p q (t, gamma))
          (strictLoopMap_refl (g.hom.comp f.hom) x))).symm
  have hBoundary : (T.trans (V.trans Uq)).Homotopic Uc :=
    loopBasepointChangeTransHomotopy_unitTriangle_homotopic p q
  have hLeft : (T.trans (V.trans Uq)).cast etaM rfl = C.trans (S.trans Ug) := by
    rw [Path.cast_trans T (V.trans Uq) etaM etaV rfl]
    rw [Path.cast_trans V Uq etaV etaG rfl]
    rw [hC, hS, hUg]
  have hNativeBoundary : (C.trans (S.trans Ug)).Homotopic Um := by
    obtain ⟨K⟩ := hBoundary
    exact ⟨(K.pathCast etaM rfl).cast hLeft hUm⟩
  let Utotal := S.trans Ug
  have hCancel : ((C.trans Utotal).trans Utotal.symm).Homotopic C :=
    (Path.Homotopic.trans_assoc C Utotal Utotal.symm).trans
      (((Path.Homotopic.refl C).hcomp (Path.Homotopic.trans_symm Utotal)).trans
        (Path.Homotopic.trans_refl C))
  exact hCancel.symm.trans
    (hNativeBoundary.hcomp (Path.Homotopic.refl Utotal.symm))

end ContinuousMap.WeaklyPointed

end
