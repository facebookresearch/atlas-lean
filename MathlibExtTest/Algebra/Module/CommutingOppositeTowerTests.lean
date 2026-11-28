/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.CommutingOpposite
public import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.NormNum

/-!
# Ground scalars and an opposite rational action

Integers act through rational scalars on a lifted rational module.
The canonical opposite action respects the ground scalar tower:
scaling the opposite rational two by three and acting on four gives
the same nonzero value twenty-four as scaling the resulting action.
-/

@[expose] public section
noncomputable section

namespace OppositeTowerExamples

private abbrev U := ULift.{1} ℚ

example :
    (letI := Module.oppositeOfCommutingAction ℚ U;
      ((3 : ℤ) • MulOpposite.op (2 : ℚ)) • (ULift.up 4 : U) =
        (3 : ℤ) • (MulOpposite.op (2 : ℚ) • (ULift.up 4 : U))) ∧
    (letI := Module.oppositeOfCommutingAction ℚ U;
      ((3 : ℤ) • MulOpposite.op (2 : ℚ)) • (ULift.up 4 : U) = ULift.up 24) := by
  letI := Module.oppositeOfCommutingAction ℚ U
  letI : IsScalarTower ℤ ℚᵐᵒᵖ U :=
    Module.oppositeOfCommutingAction_isScalarTower ℚ U (R := ℤ)
  constructor
  · exact smul_assoc (3 : ℤ) (MulOpposite.op (2 : ℚ)) (ULift.up 4 : U)
  · apply ULift.ext
    change ((3 : ℤ) • (2 : ℚ)) * (4 : ℚ) = (24 : ℚ)
    norm_num

end OppositeTowerExamples
