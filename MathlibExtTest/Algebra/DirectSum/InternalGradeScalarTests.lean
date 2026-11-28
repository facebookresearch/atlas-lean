/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.DirectSum.InternalGradeAlgebra
public import MathlibExt.Algebra.Module.CommutingOpposite
public import MathlibExt.Algebra.Polynomial.NatInterpolation
import Mathlib.Tactic.NormNum

/-!
# Integer coordinate gradings and scalar actions

The constant graded integer family has the canonical internal graded algebra
and action. Degrees one and two act into degree three with value six.
The opposite action on lifted integers retains the same scalar value.
Native coefficient vectors and their power combinations have concrete
nonzero values over the rationals.
-/

@[expose] public section
noncomputable section

open scoped DirectSum

namespace GradedScalarExamples

private abbrev GF (_ : ℕ) := ℤ

-- Select the native graded module action on the total direct sums.
local instance : Module (DirectSum ℕ GF) (DirectSum ℕ GF) :=
  DirectSum.Gmodule.module GF GF

example : GradedAlgebra (DirectSum.algebraInternalGrade ℤ GF) := inferInstance

example : SetLike.GradedSMul (DirectSum.algebraInternalGrade ℤ GF)
    (DirectSum.internalGrade ℤ ℕ GF) := inferInstance

example :
    DirectSum.of GF 1 (3 : ℤ) • DirectSum.of GF 2 (2 : ℤ) ∈
        DirectSum.internalGrade ℤ ℕ GF 3 ∧
      DirectSum.of GF 1 (3 : ℤ) • DirectSum.of GF 2 (2 : ℤ) =
        DirectSum.of GF 3 (6 : ℤ) := by
  letI : SetLike.GradedSMul (DirectSum.algebraInternalGrade ℤ GF)
      (DirectSum.internalGrade ℤ ℕ GF) := inferInstance
  constructor
  · have hx : DirectSum.of GF 1 (3 : ℤ) ∈ DirectSum.algebraInternalGrade ℤ GF 1 :=
      (DirectSum.mem_algebraInternalGrade_iff ℤ GF _ 1).mpr ⟨3, rfl⟩
    have hy : DirectSum.of GF 2 (2 : ℤ) ∈ DirectSum.internalGrade ℤ ℕ GF 2 :=
      (DirectSum.mem_internalGrade_iff ℤ ℕ GF _ 2).mpr ⟨2, rfl⟩
    exact SetLike.GradedSMul.smul_mem hx hy
  · exact DirectSum.Gmodule.of_smul_of GF GF (i := 1) (j := 2) (3 : ℤ) (2 : ℤ)

private abbrev LiftedZ := ULift.{1} ℤ

example :
    (letI := Module.oppositeOfCommutingAction ℤ LiftedZ;
      (MulOpposite.op (3 : ℤ)) • (ULift.up 2 : LiftedZ)) = ULift.up 6 := by
  calc
    (letI := Module.oppositeOfCommutingAction ℤ LiftedZ;
      (MulOpposite.op (3 : ℤ)) • (ULift.up 2 : LiftedZ)) =
        (3 : ℤ) • (ULift.up 2 : LiftedZ) :=
      Module.oppositeOfCommutingAction_smul ℤ LiftedZ
        (MulOpposite.op (3 : ℤ)) (ULift.up 2 : LiftedZ)
    _ = ULift.up 6 := by
      apply ULift.ext
      change (3 : ℤ) • (2 : ℤ) = (6 : ℤ)
      norm_num

example : (Polynomial.ofFn 2 ![(2 : ℚ), 3]).coeff 1 = 3 :=
  Polynomial.ofFn_coeff_eq_val_of_lt (n := 2) (i := 1)
    ![(2 : ℚ), 3] (by decide)

example : Polynomial.finitePowerCombination 2 ![(2 : ℚ), 3] 2 = 8 := by
  norm_num [Polynomial.finitePowerCombination,
    Polynomial.finiteWeightedPowerCombination, Fin.sum_univ_two]

end GradedScalarExamples
