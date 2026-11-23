/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopMultiplication
public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison
public import MathlibExt.Topology.Homotopy.IntervalPathSpaceHomotopy

/-!
# The original root-pair unit path and the actual joint root contraction

The SAME original own-unit homotopy is mapped from its SAME universal
interval homotopy. The actual interval path-space comparison then identifies
its original unit Path with SAME201 contraction, through derived endpoints.
Both full original families and all original time coordinates are retained.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- The ACTUAL original root-pair unit Path is homotopic to SAME201
joint contraction of its SAME original root, with derived actual unit cast.
Every original choice and both original time coordinates remain. -/
theorem loopMapUnitPath_homotopic_rootUnit (f : WeaklyPointed x y) :
    (loopMapUnitPath f).Homotopic
      (((rootUnitContraction (fun r : Path (f.hom x) y => r) continuous_eval).evalAt
        f.rootPath).cast (loopMapUnit_eq_rootUnitLoopFamily f.hom f.rootPath) rfl) := by
  let p := f.rootPath
  let q : Path (0 : I) (1 : I) := Path.id
  let fi : WeaklyPointed (0 : I) (1 : I) := ⟨ContinuousMap.id I, q⟩
  let P := loopMapUnitPath f
  let PI := loopMapUnitPath fi
  let Q := ((rootUnitContraction (fun r : Path (f.hom x) y => r) continuous_eval).evalAt
    p).cast (loopMapUnit_eq_rootUnitLoopFamily f.hom p) rfl
  let QI := ((rootUnitContraction (fun r : Path (0 : I) (1 : I) => r)
    continuous_eval).evalAt q).cast
      (loopMapUnit_eq_rootUnitLoopFamily (ContinuousMap.id I) q) rfl
  let W : C(LoopSpace I (1 : I), LoopSpace Y y) :=
    { toFun := fun gamma => (gamma.map p.continuous).cast p.target.symm p.target.symm
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z : LoopSpace I (1 : I) × I => p (z.1 z.2))
        exact p.continuous.comp continuous_eval }
  have hP (t : I) : P.toContinuousMap.toFun t = W (PI.toContinuousMap.toFun t) := by
    apply Path.ext
    funext s
    have hTemplate := loopMapUnitHomotopy_template f t
    exact (loopMapUnitPath_apply f t s).trans
      ((congrArg (fun gamma : LoopSpace Y y => gamma s) hTemplate).trans
        (congrArg p (loopMapUnitPath_apply fi t s)).symm)
  have hSource : f.loopMap (Path.refl x) = W (fi.loopMap (Path.refl (0 : I))) :=
    P.source.symm.trans ((hP 0).trans (congrArg W PI.source))
  have hTarget : Path.refl y = W (Path.refl (1 : I)) :=
    P.target.symm.trans ((hP 1).trans (congrArg W PI.target))
  have hQ (t : I) : Q.toContinuousMap.toFun t = W (QI.toContinuousMap.toFun t) := by
    apply Path.ext
    funext s
    change rootUnitContraction (fun r : Path (f.hom x) y => r) continuous_eval (t, p) s =
      p (rootUnitContraction (fun r : Path (0 : I) (1 : I) => r)
        continuous_eval (t, q) s)
    have hY := rootUnitContraction_apply
      (fun r : Path (f.hom x) y => r) continuous_eval t p s
    have hI := rootUnitContraction_apply
      (fun r : Path (0 : I) (1 : I) => r) continuous_eval t q s
    exact hY.trans (congrArg p hI).symm
  have hLeft : (PI.map W.continuous).cast hSource hTarget = P := by
    apply Path.ext
    funext t
    exact (hP t).symm
  have hRight : (QI.map W.continuous).cast hSource hTarget = Q := by
    apply Path.ext
    funext t
    exact (hQ t).symm
  let K := (Path.intervalPathSpaceHomotopy PI QI).map W
  exact ⟨(K.pathCast hSource hTarget).cast hLeft hRight⟩

end ContinuousMap.WeaklyPointed

end
