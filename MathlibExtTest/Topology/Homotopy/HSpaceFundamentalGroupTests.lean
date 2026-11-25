/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Topology.Homotopy.HSpaceFundamentalGroup

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

#check HSpace.pathMul
#check HSpace.pathMulHomotopy
#check HSpace.fundamentalMul
#check HSpace.fundamentalMul_mk
#check HSpace.fundamentalMul_one_left
#check HSpace.fundamentalMul_one_right
#check HSpace.pathMul_trans
#check HSpace.fundamentalMul_trans
#check HSpace.fundamentalMul_interchange
#check HSpace.fundamentalMul_isUnital
#check HSpace.fundamentalGroupCommGroup
#check HSpace.fundamentalGroup_mul_comm

example (p q : FundamentalGroup X HSpace.e) : p * q = q * p :=
  HSpace.fundamentalGroup_mul_comm p q

example (p q : FundamentalGroup ℝ (HSpace.e : ℝ)) : p * q = q * p :=
  HSpace.fundamentalGroup_mul_comm p q

example (p q : FundamentalGroup (ℝ × ℝ) (HSpace.e : ℝ × ℝ)) :
    p * q = q * p :=
  HSpace.fundamentalGroup_mul_comm p q

noncomputable example : CommGroup (FundamentalGroup X HSpace.e) :=
  HSpace.fundamentalGroupCommGroup

#print axioms HSpace.pathMul
#print axioms HSpace.pathMul_apply
#print axioms HSpace.pathMulHomotopy
#print axioms HSpace.fundamentalMul
#print axioms HSpace.fundamentalMul_mk
#print axioms HSpace.pathMulReflLeftHomotopy
#print axioms HSpace.pathMulReflRightHomotopy
#print axioms HSpace.fundamentalMul_one_left
#print axioms HSpace.fundamentalMul_one_right
#print axioms HSpace.pathMul_trans
#print axioms HSpace.fundamentalMul_trans
#print axioms HSpace.fundamentalMul_interchange
#print axioms HSpace.fundamentalMul_isUnital
#print axioms HSpace.fundamentalGroupCommGroup
#print axioms HSpace.fundamentalGroup_mul_comm

#check @HSpace.fundamentalGroup_mul_comm_at_point
#print axioms HSpace.fundamentalGroup_mul_comm_at_point

example [PathConnectedSpace X] (x : X) (a b : FundamentalGroup X x) : a * b = b * a :=
  HSpace.fundamentalGroup_mul_comm_at_point x a b

end
