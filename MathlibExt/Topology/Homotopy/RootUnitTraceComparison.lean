/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction

/-!
# Actual chosen-root homotopy unit traces

The original weakly pointed root-path homotopy, at the original constant
source loop, has the unit trace obtained from the same chosen root family.
Its endpoint comparison uses the accepted joint root-unit contraction and
the actual strict mapped-unit equations. Both endpoint casts are derived;
the chosen root homotopy and the contraction are retained.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

private theorem originalRootMapUnitEndpointComputed
    (f : C(X, Y)) (p : Path (f x) y) :
    (⟨f, p⟩ : WeaklyPointed x y).loopMap (Path.refl x) =
      rootUnitLoopFamily (fun r : Path (f x) y => r) continuous_eval p := by
  have h := congrArg (fun k : C(LoopSpace X x, LoopSpace Y y) => k (Path.refl x))
    (loopMap_eq_loopBasepointChange_comp_strictLoopMap (⟨f, p⟩ : WeaklyPointed x y))
  exact h.trans
    ((congrArg (loopBasepointChange p) (strictLoopMap_refl f x)).trans
      (rootUnitLoopFamily_pathSpace_apply p).symm)

/-- The actual weakly pointed unit image is the original whole unit
loop of the same root, through the strict mapped-unit equation. -/
theorem loopMapUnit_eq_rootUnitLoopFamily (f : C(X, Y)) (p : Path (f x) y) :
    (⟨f, p⟩ : WeaklyPointed x y).loopMap (Path.refl x) =
      rootUnitLoopFamily (fun r : Path (f x) y => r) continuous_eval p :=
  originalRootMapUnitEndpointComputed f p

private theorem originalLoopMapRootUnitTraceComputed (f : C(X, Y))
    {p q : Path (f x) y} (H : p.Homotopy q) :
    ((loopMapRootPathHomotopy f H).evalAt (Path.refl x)).Homotopic
      ((((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt p).trans
        ((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt q).symm).cast
          (loopMapUnit_eq_rootUnitLoopFamily f p)
          (loopMapUnit_eq_rootUnitLoopFamily f q)) := by
  let etaP := (loopMapUnit_eq_rootUnitLoopFamily f p).trans
    (rootUnitLoopFamily_pathSpace_apply p)
  let etaQ := (loopMapUnit_eq_rootUnitLoopFamily f q).trans
    (rootUnitLoopFamily_pathSpace_apply q)
  let R :=
    ((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt p).trans
      ((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt q).symm
  obtain ⟨K⟩ := rootUnitContraction_rootPathHomotopy H
  let K' := K.pathCast etaP etaQ
  have hTrace : ((loopBasepointChangePathHomotopy H).evalAt
      (Path.refl (f x))).cast etaP etaQ =
      (loopMapRootPathHomotopy f H).evalAt (Path.refl x) := by
    apply Path.ext
    funext t
    change loopBasepointChangePathHomotopy H (t, Path.refl (f x)) =
      loopMapRootPathHomotopy f H (t, Path.refl x)
    have hB := loopBasepointChangePathHomotopy_apply H t (Path.refl (f x))
    have hW := loopMapRootPathHomotopy_apply f H t (Path.refl x)
    have hM := congrArg (fun gamma : LoopSpace Y (f x) =>
      (H.eval t).symm.trans (gamma.trans (H.eval t))) (strictLoopMap_refl f x)
    exact hB.trans (hW.trans hM).symm
  have hTarget :
      ((R.cast (rootUnitLoopFamily_pathSpace_apply p).symm
        (rootUnitLoopFamily_pathSpace_apply q).symm).cast etaP etaQ) =
      R.cast (loopMapUnit_eq_rootUnitLoopFamily f p)
        (loopMapUnit_eq_rootUnitLoopFamily f q) := by
    apply Path.ext
    funext t
    rfl
  exact ⟨K'.cast hTrace hTarget⟩

/-- The actual original first-piece unit trace is compared through the
same joint contraction and chosen root homotopy, with derived endpoint casts. -/
theorem loopMapRootPathHomotopy_unitTrace_homotopic (f : C(X, Y))
    {p q : Path (f x) y} (H : p.Homotopy q) :
    ((loopMapRootPathHomotopy f H).evalAt (Path.refl x)).Homotopic
      ((((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt p).trans
        ((rootUnitContraction (fun r : Path (f x) y => r) continuous_eval).evalAt q).symm).cast
          (loopMapUnit_eq_rootUnitLoopFamily f p)
          (loopMapUnit_eq_rootUnitLoopFamily f q)) :=
  originalLoopMapRootUnitTraceComputed f H

end ContinuousMap.WeaklyPointed

end
