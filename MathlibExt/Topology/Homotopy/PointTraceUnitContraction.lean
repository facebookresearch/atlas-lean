/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv

/-!
# Actual moving point-trace unit comparison

The original remaining point trace supplies a moving-source root family.
Naturality in the same joint root-unit contraction compares its actual
unit-loop trace with the contraction of the full original point trace.
The final tail and its contraction are derived reflexive and constant.
The original half-clock branches and target-root postcomposition remain
the same complete paths, with their actual endpoint casts.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.Homotopy

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

private def originalMovingTailUnitPathComputed (H : Homotopy f g) (x : X) :
    Path (loopBasepointChange (H.evalAt x) (Path.refl (f x))) (Path.refl (g x)) where
  toFun t := traceLoopFamily H x (t, Path.refl x)
  continuous_toFun := (traceLoopFamily H x).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := (traceLoopFamily_zero H x (Path.refl x)).trans
    (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x))
  target' := by
    have h : loopBasepointChange (Path.refl (g x)) (Path.refl (g x)) =
        Path.refl (g x) := by
      rw [loopBasepointChange_apply, Path.refl_symm, Path.refl_trans_refl,
        Path.refl_trans_refl]
    exact (traceLoopFamily_one H x (Path.refl x)).trans
      ((congrArg (loopBasepointChange (Path.refl (g x)))
        (strictLoopMap_refl g x)).trans h)

private theorem originalMovingPointTraceUnitComputed (H : Homotopy f g) (x : X) :
    (((traceConjugationLoopHomotopy H x).evalAt (Path.refl x)).cast
      (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x)).symm
      (strictLoopMap_refl g x).symm).Homotopic
      (((rootUnitContraction (fun r : Path (f x) (g x) => r)
        continuous_eval).evalAt (H.evalAt x)).cast
          (rootUnitLoopFamily_pathSpace_apply (H.evalAt x)).symm rfl) := by
  let p : ∀ t : I, Path (H (t, x)) (g x) := fun t => pointTraceTail H x t
  let hp : Continuous (fun z : I × I => p z.1 z.2) := pointTraceTail_continuous H x
  let e : LoopSpace Y (g x) := Path.refl (g x)
  let L : C(I, LoopSpace Y (g x)) := rootUnitLoopFamily p hp
  let U : Homotopy L (ContinuousMap.const I e) := rootUnitContraction p hp
  let E : Path (L 0) (L 1) := Path.id.map L.continuous
  let T := originalMovingTailUnitPathComputed H x
  have hL0 : L 0 = traceLoopFamily H x (0, Path.refl x) :=
    (rootUnitLoopFamily_shape p hp 0).trans
      (traceLoopFamily_refl_eq_pointTraceTail H x 0).symm
  have hStart : loopBasepointChange (H.evalAt x) (Path.refl (f x)) = L 0 :=
    (hL0.trans ((traceLoopFamily_zero H x (Path.refl x)).trans
      (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x)))).symm
  have hTailOne (s : I) : p 1 s = g x :=
    congrArg (fun r : Path (g x) (g x) => r s) (pointTraceTail_one H x)
  have hEnd : L 1 = e := by
    apply Path.ext
    funext s
    exact (rootUnitLoopFamily_apply p hp 1 s).trans (hTailOne (rootUnitClock s))
  have hLast : (U.evalAt 1).cast hEnd.symm rfl = Path.refl e := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    change rootUnitContraction p hp (t, 1) s = g x
    exact (rootUnitContraction_apply p hp t 1 s).trans
      (hTailOne (Set.Icc.convexComb (rootUnitClock s) 1 t))
  let Ea : Path (loopBasepointChange (H.evalAt x) (Path.refl (f x))) e :=
    E.cast hStart hEnd.symm
  let Ua : Path (loopBasepointChange (H.evalAt x) (Path.refl (f x))) e :=
    (U.evalAt 0).cast hStart rfl
  have hConst : Path.id.map (ContinuousMap.const I e).continuous = Path.refl e := by
    apply Path.ext
    funext t
    rfl
  have hLeft : (E.trans (U.evalAt 1)).cast hStart rfl = Ea.trans (Path.refl e) :=
    (Path.cast_trans E (U.evalAt 1) hStart hEnd.symm rfl).trans
      (congrArg (fun r : Path e e => Ea.trans r) hLast)
  have hRight : ((U.evalAt 0).trans
      (Path.id.map (ContinuousMap.const I e).continuous)).cast hStart rfl =
      Ua.trans (Path.refl e) :=
    (Path.cast_trans (U.evalAt 0)
      (Path.id.map (ContinuousMap.const I e).continuous) hStart rfl rfl).trans
        (congrArg (fun r : Path e e => Ua.trans r) hConst)
  obtain ⟨V⟩ := Path.Homotopic.map_trans_evalAt U Path.id
  have hNat : (Ea.trans (Path.refl e)).Homotopic (Ua.trans (Path.refl e)) :=
    ⟨(V.pathCast hStart rfl).cast hLeft hRight⟩
  have hMoving : Ea.Homotopic Ua :=
    (Path.Homotopic.trans_refl Ea).symm.trans
      (hNat.trans (Path.Homotopic.trans_refl Ua))
  have hTrace : T = Ea := by
    apply Path.ext
    funext t
    change traceLoopFamily H x (t, Path.refl x) = rootUnitLoopFamily p hp t
    exact (traceLoopFamily_refl_eq_pointTraceTail H x t).trans
      (rootUnitLoopFamily_shape p hp t).symm
  let W : Path (loopBasepointChange (H.evalAt x) (Path.refl (f x))) e :=
    ((rootUnitContraction (fun r : Path (f x) (g x) => r)
      continuous_eval).evalAt (H.evalAt x)).cast
        (rootUnitLoopFamily_pathSpace_apply (H.evalAt x)).symm rfl
  have hZeroContraction : Ua = W := by
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    change rootUnitContraction p hp (t, 0) s =
      rootUnitContraction (fun r : Path (f x) (g x) => r) continuous_eval
        (t, H.evalAt x) s
    let c := Set.Icc.convexComb (rootUnitClock s) 1 t
    have hz : p 0 c = H.evalAt x c :=
      congrArg (fun r : Path (f x) (g x) => r c) (pointTraceTail_zero H x)
    exact (rootUnitContraction_apply p hp t 0 s).trans
      (hz.trans (rootUnitContraction_apply (fun r : Path (f x) (g x) => r)
        continuous_eval t (H.evalAt x) s).symm)
  obtain ⟨J⟩ := hMoving
  have hT : T.Homotopic W := ⟨J.cast hTrace.symm hZeroContraction⟩
  let A : Path (loopBasepointChange (H.evalAt x) (Path.refl (f x))) e :=
    ((traceConjugationLoopHomotopy H x).evalAt (Path.refl x)).cast
      (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x)).symm
      (strictLoopMap_refl g x).symm
  have hFull : A = T.trans (Path.refl e) := by
    apply Path.ext
    funext t
    change traceConjugationLoopHomotopy H x (t, Path.refl x) =
      (T.trans (Path.refl e)) t
    rw [Path.trans_apply]
    exact traceConjugationLoopHomotopy_refl_piecewise H x t
  obtain ⟨Jfull⟩ := (Path.Homotopic.trans_refl T).trans hT
  exact ⟨Jfull.cast hFull.symm rfl⟩

/-- The actual original moving-source unit trace is compared with the
same joint contraction of the entire original point trace. -/
theorem traceConjugationLoopHomotopy_unitTrace_homotopic (H : Homotopy f g) (x : X) :
    (((traceConjugationLoopHomotopy H x).evalAt (Path.refl x)).cast
      (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x)).symm
      (strictLoopMap_refl g x).symm).Homotopic
      (((rootUnitContraction (fun r : Path (f x) (g x) => r)
        continuous_eval).evalAt (H.evalAt x)).cast
          (rootUnitLoopFamily_pathSpace_apply (H.evalAt x)).symm rfl) :=
  originalMovingPointTraceUnitComputed H x

private theorem originalPostcomposedPointTraceUnitComputed
    (H : Homotopy f g) (x : X) {y : Y} (q : Path (g x) y) :
    ((((Homotopy.refl (loopBasepointChange q)).comp
      (traceConjugationLoopHomotopy H x)).evalAt (Path.refl x)).cast
        (congrArg (loopBasepointChange q)
          (congrArg (loopBasepointChange (H.evalAt x))
            (strictLoopMap_refl f x))).symm
        (congrArg (loopBasepointChange q) (strictLoopMap_refl g x)).symm).Homotopic
      ((((rootUnitContraction (fun r : Path (f x) (g x) => r)
        continuous_eval).evalAt (H.evalAt x)).cast
          (rootUnitLoopFamily_pathSpace_apply (H.evalAt x)).symm rfl).map
            (loopBasepointChange q).continuous) := by
  let A := ((traceConjugationLoopHomotopy H x).evalAt (Path.refl x)).cast
    (congrArg (loopBasepointChange (H.evalAt x)) (strictLoopMap_refl f x)).symm
    (strictLoopMap_refl g x).symm
  obtain ⟨K⟩ := traceConjugationLoopHomotopy_unitTrace_homotopic H x
  have hActual :
      ((((Homotopy.refl (loopBasepointChange q)).comp
        (traceConjugationLoopHomotopy H x)).evalAt (Path.refl x)).cast
          (congrArg (loopBasepointChange q)
            (congrArg (loopBasepointChange (H.evalAt x))
              (strictLoopMap_refl f x))).symm
          (congrArg (loopBasepointChange q) (strictLoopMap_refl g x)).symm) =
      A.map (loopBasepointChange q).continuous := by
    apply Path.ext
    funext t
    rfl
  exact ⟨(K.map (loopBasepointChange q)).cast hActual.symm rfl⟩

/-- The whole actual third-piece unit trace after the same target root
retains its actual root-conjugated target unit image and derived endpoint casts. -/
theorem traceConjugationLoopHomotopy_postcomp_unitTrace_homotopic
    (H : Homotopy f g) (x : X) {y : Y} (q : Path (g x) y) :
    ((((Homotopy.refl (loopBasepointChange q)).comp
      (traceConjugationLoopHomotopy H x)).evalAt (Path.refl x)).cast
        (congrArg (loopBasepointChange q)
          (congrArg (loopBasepointChange (H.evalAt x))
            (strictLoopMap_refl f x))).symm
        (congrArg (loopBasepointChange q) (strictLoopMap_refl g x)).symm).Homotopic
      ((((rootUnitContraction (fun r : Path (f x) (g x) => r)
        continuous_eval).evalAt (H.evalAt x)).cast
          (rootUnitLoopFamily_pathSpace_apply (H.evalAt x)).symm rfl).map
            (loopBasepointChange q).continuous) :=
  originalPostcomposedPointTraceUnitComputed H x q

end ContinuousMap.Homotopy

end
