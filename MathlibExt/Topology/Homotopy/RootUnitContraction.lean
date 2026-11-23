/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopies
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Joint contraction of the original root-unit loop family

A whole continuous family of roots may have a moving source point and a
fixed target point. The original reverse-root, reflexive segment and root
loop contracts continuously over every family parameter and both time
coordinates. Homotopy naturality compares the actual chosen root-homotopy
unit trace with the endpoint contractions, without changing that choice.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

/-- The interval coordinate of the original three-piece root-unit loop. -/
def rootUnitClock : Path (1 : I) (1 : I) :=
  (Path.id : Path (0 : I) (1 : I)).symm.trans
    ((Path.refl (0 : I)).trans (Path.id : Path (0 : I) (1 : I)))

private theorem originalRootUnitClockValueComputed (s : I) :
    (rootUnitClock s : ℝ) =
      if (s : ℝ) ≤ 1 / 2 then 1 - 2 * (s : ℝ)
      else if 2 * (s : ℝ) - 1 ≤ 1 / 2 then 0
      else 2 * (2 * (s : ℝ) - 1) - 1 := by
  simp only [rootUnitClock, Path.trans_apply, Path.symm_apply,
    Path.refl_apply, Path.id_apply]
  split_ifs <;> rfl

/-- The actual nested concatenation clocks have cuts at one half and
three quarters, including both exact joining values. -/
theorem rootUnitClock_coe (s : I) :
    (rootUnitClock s : ℝ) =
      if (s : ℝ) ≤ 1 / 2 then 1 - 2 * (s : ℝ)
      else if 2 * (s : ℝ) - 1 ≤ 1 / 2 then 0
      else 2 * (2 * (s : ℝ) - 1) - 1 :=
  originalRootUnitClockValueComputed s

section MovingRoots

variable {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
  {x : A → Y} {y : Y}

omit [TopologicalSpace A] in
private theorem originalRootUnitLoopValueComputed
    (p : ∀ a : A, Path (x a) y) (a : A) (s : I) :
    ((p a).symm.trans ((Path.refl (x a)).trans (p a))) s =
      p a (rootUnitClock s) := by
  simp only [rootUnitClock, Path.trans_apply, Path.symm_apply,
    Path.refl_apply, Path.id_apply]
  split_ifs <;> first | rfl | exact (p a).source.symm

/-- The whole original three-piece unit loop for a continuously varying
root source point and the original fixed target point. -/
def rootUnitLoopFamily (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) : C(A, LoopSpace Y y) where
  toFun a := (p a).symm.trans ((Path.refl (x a)).trans (p a))
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have h : Continuous (fun z : A × I => p z.1 (rootUnitClock z.2)) :=
      hp.comp (continuous_fst.prodMk (rootUnitClock.continuous.comp continuous_snd))
    exact h.congr (fun z => (originalRootUnitLoopValueComputed p z.1 z.2).symm)

private theorem originalRootUnitFamilyShapeComputed
    (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (a : A) :
    rootUnitLoopFamily p hp a =
      (p a).symm.trans ((Path.refl (x a)).trans (p a)) := rfl

/-- The entire source loop retains the original root and parenthesized
reverse-root, reflexive-segment, root concatenation. -/
theorem rootUnitLoopFamily_shape (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (a : A) :
    rootUnitLoopFamily p hp a =
      (p a).symm.trans ((Path.refl (x a)).trans (p a)) :=
  originalRootUnitFamilyShapeComputed p hp a

/-- Every original family parameter and loop time use the actual common
three-piece interval coordinate. -/
theorem rootUnitLoopFamily_apply (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (a : A) (s : I) :
    rootUnitLoopFamily p hp a s = p a (rootUnitClock s) :=
  (congrArg (fun gamma : LoopSpace Y y => gamma s)
    (rootUnitLoopFamily_shape p hp a)).trans (originalRootUnitLoopValueComputed p a s)

private def originalRootUnitContractionComputed
    (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) :
    Homotopy (rootUnitLoopFamily p hp) (ContinuousMap.const A (Path.refl y)) where
  toFun z :=
    { toFun := fun s => p z.2 (Set.Icc.convexComb (rootUnitClock s) 1 z.1)
      continuous_toFun := (p z.2).continuous.comp
        (Set.Icc.continuous_convexComb_prod.comp
          (rootUnitClock.continuous.prodMk (continuous_const.prodMk continuous_const)))
      source' := by
        rw [rootUnitClock.source, Set.Icc.convexComb_eq]
        exact (p z.2).target
      target' := by
        rw [rootUnitClock.target, Set.Icc.convexComb_eq]
        exact (p z.2).target }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hTime : Continuous (fun z : (I × A) × I =>
        Set.Icc.convexComb (rootUnitClock z.2) 1 z.1.1) :=
      Set.Icc.continuous_convexComb_prod.comp
        ((rootUnitClock.continuous.comp continuous_snd).prodMk
          (continuous_const.prodMk (continuous_fst.comp continuous_fst)))
    exact hp.comp ((continuous_snd.comp continuous_fst).prodMk hTime)
  map_zero_left a := by
    apply Path.ext
    funext s
    change p a (Set.Icc.convexComb (rootUnitClock s) 1 0) = rootUnitLoopFamily p hp a s
    exact (congrArg (p a) (Set.Icc.convexComb_zero (rootUnitClock s) 1)).trans
      (rootUnitLoopFamily_apply p hp a s).symm
  map_one_left a := by
    apply Path.ext
    funext s
    change p a (Set.Icc.convexComb (rootUnitClock s) 1 1) = y
    exact (congrArg (p a) (Set.Icc.convexComb_one (rootUnitClock s) 1)).trans (p a).target

/-- One jointly continuous contraction over the actual whole root
family, allowing its source point to move and keeping its target fixed. -/
def rootUnitContraction (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) :
    Homotopy (rootUnitLoopFamily p hp) (ContinuousMap.const A (Path.refl y)) :=
  originalRootUnitContractionComputed p hp

private theorem originalRootUnitContractionValueComputed
    (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (t : I) (a : A) (s : I) :
    rootUnitContraction p hp (t, a) s =
      p a (Set.Icc.convexComb (rootUnitClock s) 1 t) := rfl

/-- All three original coordinates use the same root family and the
actual three-piece coordinate, with its turn moved toward the fixed target. -/
theorem rootUnitContraction_apply (p : ∀ a : A, Path (x a) y)
    (hp : Continuous (fun z : A × I => p z.1 z.2)) (t : I) (a : A) (s : I) :
    rootUnitContraction p hp (t, a) s =
      p a (Set.Icc.convexComb (rootUnitClock s) 1 t) :=
  originalRootUnitContractionValueComputed p hp t a s

end MovingRoots

section RootTrace

variable {Y : Type v} [TopologicalSpace Y] {x y : Y} {p q : Path x y}

private theorem originalRootUnitPathSpaceEndpointComputed (r : Path x y) :
    rootUnitLoopFamily (fun r : Path x y => r) continuous_eval r =
      loopBasepointChange r (Path.refl x) :=
  (rootUnitLoopFamily_shape (fun r : Path x y => r) continuous_eval r).trans
    (loopBasepointChange_apply r (Path.refl x)).symm

/-- The whole path-space unit-family endpoint is the actual original
root-conjugated unit loop, through its public three-piece formula. -/
theorem rootUnitLoopFamily_pathSpace_apply (r : Path x y) :
    rootUnitLoopFamily (fun r : Path x y => r) continuous_eval r =
      loopBasepointChange r (Path.refl x) :=
  originalRootUnitPathSpaceEndpointComputed r

private theorem originalRootPathUnitTraceComputed (H : p.Homotopy q) :
    ((loopBasepointChangePathHomotopy H).evalAt (Path.refl x)).Homotopic
      (((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt p).trans
        ((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt q).symm) := by
  let L : C(Path x y, LoopSpace Y y) :=
    rootUnitLoopFamily (fun r : Path x y => r) continuous_eval
  let U : Homotopy L (ContinuousMap.const (Path x y) (Path.refl y)) :=
    rootUnitContraction (fun r : Path x y => r) continuous_eval
  let E : Path p q :=
    { toFun := H.eval
      continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous_toFun
      source' := Path.Homotopy.eval_zero H
      target' := Path.Homotopy.eval_one H }
  let T := (loopBasepointChangePathHomotopy H).evalAt (Path.refl x)
  let Up := U.evalAt p
  let Uq := U.evalAt q
  have hTrace : E.map L.continuous = T := by
    apply Path.ext
    funext t
    change rootUnitLoopFamily (fun r : Path x y => r) continuous_eval (H.eval t) =
      loopBasepointChangePathHomotopy H (t, Path.refl x)
    exact (rootUnitLoopFamily_shape (fun r : Path x y => r) continuous_eval (H.eval t)).trans
      (loopBasepointChangePathHomotopy_apply H t (Path.refl x)).symm
  have hConst : E.map (ContinuousMap.const (Path x y) (Path.refl y)).continuous =
      Path.refl (Path.refl y) := by
    apply Path.ext
    funext t
    rfl
  have hNat : (T.trans Uq).Homotopic (Up.trans (Path.refl (Path.refl y))) := by
    obtain ⟨V⟩ := Path.Homotopic.map_trans_evalAt U E
    exact ⟨V.cast
      (congrArg (fun r : Path (L p) (L q) => r.trans Uq) hTrace)
      (congrArg (fun r : Path (Path.refl y) (Path.refl y) => Up.trans r) hConst)⟩
  have hCancel : ((T.trans Uq).trans Uq.symm).Homotopic T :=
    (Path.Homotopic.trans_assoc T Uq Uq.symm).trans
      (((Path.Homotopic.refl T).hcomp (Path.Homotopic.trans_symm Uq)).trans
        (Path.Homotopic.trans_refl T))
  exact hCancel.symm.trans
    ((hNat.hcomp (Path.Homotopic.refl Uq.symm)).trans
      ((Path.Homotopic.trans_refl Up).hcomp (Path.Homotopic.refl Uq.symm)))

private theorem originalRootPathUnitTraceCastedComputed (H : p.Homotopy q) :
    ((loopBasepointChangePathHomotopy H).evalAt (Path.refl x)).Homotopic
      ((((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt p).trans
        ((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt q).symm).cast
          (rootUnitLoopFamily_pathSpace_apply p).symm
          (rootUnitLoopFamily_pathSpace_apply q).symm) := by
  obtain ⟨K⟩ := originalRootPathUnitTraceComputed H
  refine ⟨K.cast rfl ?_⟩
  apply Path.ext
  funext t
  rfl

/-- The actual chosen root-homotopy unit trace is compared by naturality
in the entire joint contraction, with derived actual endpoint casts. -/
theorem rootUnitContraction_rootPathHomotopy (H : p.Homotopy q) :
    ((loopBasepointChangePathHomotopy H).evalAt (Path.refl x)).Homotopic
      ((((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt p).trans
        ((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt q).symm).cast
          (rootUnitLoopFamily_pathSpace_apply p).symm
          (rootUnitLoopFamily_pathSpace_apply q).symm) :=
  originalRootPathUnitTraceCastedComputed H

end RootTrace

end ContinuousMap

end
