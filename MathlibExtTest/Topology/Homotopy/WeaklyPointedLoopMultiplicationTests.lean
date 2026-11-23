/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopMultiplication
public import Mathlib.Tactic.NormNum

/-!
# Weakly pointed multiplication with a nonconstant chosen root
-/

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

namespace WeaklyPointedLoopMultiplicationTests

private def risingRoot : Path (0 : ℝ) 1 where
  toFun t := (t : ℝ)
  continuous_toFun := continuous_subtype_val
  source' := rfl
  target' := rfl

private def bumpLoop : Path (0 : ℝ) 0 where
  toFun t := (t : ℝ) * (1 - (t : ℝ))
  continuous_toFun := by fun_prop
  source' := by norm_num
  target' := by norm_num

private theorem risingRoot_value (t : I) : risingRoot t = (t : ℝ) := rfl

private theorem risingRoot_symm_value (t : I) : risingRoot.symm t = 1 - (t : ℝ) := rfl

private theorem bumpLoop_value (t : I) : bumpLoop t = (t : ℝ) * (1 - (t : ℝ)) := rfl

private theorem mappedBump_value (t : I) :
    (bumpLoop.map continuous_id) t =
      (t : ℝ) * (1 - (t : ℝ)) := rfl

private def rootedIdentity : ContinuousMap.WeaklyPointed (0 : ℝ) (1 : ℝ) where
  hom := ⟨fun x : ℝ => x, continuous_id⟩
  rootPath := risingRoot

example : rootedIdentity.loopMap bumpLoop (⟨1 / 4, by norm_num⟩ : I) = 1 / 2 := by
  norm_num [ContinuousMap.WeaklyPointed.loopMap_apply, Path.trans_apply, Path.symm_apply,
    Path.map_coe, Function.comp_apply, rootedIdentity, risingRoot_value,
    risingRoot_symm_value, bumpLoop_value, mappedBump_value]
  rw [risingRoot_value]
  norm_num [unitInterval.coe_symm_eq]

example : rootedIdentity.loopMap bumpLoop (⟨5 / 8, by norm_num⟩ : I) = 1 / 4 := by
  norm_num [ContinuousMap.WeaklyPointed.loopMap_apply, Path.trans_apply, Path.symm_apply,
    Path.map_coe, Function.comp_apply, rootedIdentity, risingRoot_value,
    risingRoot_symm_value, bumpLoop_value, mappedBump_value]
  rw [bumpLoop_value]
  norm_num

example : ContinuousMap.WeaklyPointed.loopMapMultiplicationHomotopy rootedIdentity
    (0, (bumpLoop, bumpLoop.symm)) =
      rootedIdentity.loopMap (bumpLoop.trans bumpLoop.symm) := by
  exact (ContinuousMap.WeaklyPointed.loopMapMultiplicationHomotopy rootedIdentity).map_zero_left _

example : ContinuousMap.WeaklyPointed.loopMapMultiplicationHomotopy rootedIdentity
    (1, (bumpLoop, bumpLoop.symm)) =
      (rootedIdentity.loopMap bumpLoop).trans (rootedIdentity.loopMap bumpLoop.symm) := by
  exact (ContinuousMap.WeaklyPointed.loopMapMultiplicationHomotopy rootedIdentity).map_one_left _

example : rootedIdentity.loopMapUnitPath 0 = rootedIdentity.loopMap (Path.refl 0) :=
  rootedIdentity.loopMapUnitPath.source

example : rootedIdentity.loopMapUnitPath 1 = Path.refl 1 :=
  rootedIdentity.loopMapUnitPath.target

end WeaklyPointedLoopMultiplicationTests

end
