/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopShiftNaturality

/-!
# Independent-space clients of the canonical chosen-root loop shift

These arbitrary-space clients import topology directly. They retain both
original unit clocks, the canonical positive maps and the full root shift.
-/

public section
noncomputable section

open CategoryTheory Topology
open scoped ContinuousMap unitInterval Topology.Homotopy

universe uX uY

namespace WeaklyPointedLoopShiftNaturalityTests

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Every unit time and loop time follows the same original joint contraction. -/
theorem original_unit_full_value (f : ContinuousMap.WeaklyPointed x y)
    (t s : unitInterval) :
    ContinuousMap.WeaklyPointed.loopUnitRootPath f t s =
      ContinuousMap.rootUnitContraction (fun p : Path (f.hom x) y => p)
        continuous_eval (t, f.rootPath) s :=
  ContinuousMap.WeaklyPointed.originalLoopOwnUnit_value201 f t s

/-- The whole canonical positive loop map agrees with the same map using
the exact own-unit recipe; both original paths are retained. -/
theorem original_positive_loop_map (n : ℕ) (f : ContinuousMap.WeaklyPointed x y) :
    ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap n f =
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
        (⟨f.loopMap, ContinuousMap.WeaklyPointed.loopUnitRootPath f⟩ :
          ContinuousMap.WeaklyPointed (Path.refl x) (Path.refl y)) := by
  have hUnit : (ContinuousMap.WeaklyPointed.loopMapUnitPath f).Homotopic
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f) := by
    rw [ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201]
    exact ContinuousMap.WeaklyPointed.loopMapUnitPath_homotopic_rootUnit f
  apply MonoidHom.ext
  intro a
  rw [ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap_apply,
    ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply]
  exact congrArg (fun e => e (HomotopyGroup.map f.loopMap a))
    (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n
      (TopCat.of (LoopSpace Y y)) hUnit)

/-- An arbitrary root between independent spaces retains its original
positive shift and whole chosen-root transport. -/
theorem independentRootedShift_client (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y y
        (ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
          (⟨f.loopMap, ContinuousMap.WeaklyPointed.loopUnitRootPath f⟩ :
            ContinuousMap.WeaklyPointed (Path.refl x) (Path.refl y)) a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom (HomotopyGroup.loopShiftMulEquiv n X x a)) :=
  HomotopyGroup.loopShiftMulEquiv_rooted_naturality n f a

/-- The existing canonical positive-loop map has the same original-root
shift square without a K-theory import or a supplied comparison premise. -/
theorem existingPositiveLoopShift_client (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y y
        (ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap n f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom (HomotopyGroup.loopShiftMulEquiv n X x a)) :=
  HomotopyGroup.loopShiftMulEquiv_positiveLoop_naturality n f a

end WeaklyPointedLoopShiftNaturalityTests

end
