/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspFormGamma0Two

@[expose] public section

open scoped UpperHalfPlane

example : (CongruenceSubgroup.Gamma0 2).index = 3 :=
  CongruenceSubgroup.Gamma0_two_index_eq_three

example (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  ModularForm.S2_Gamma0_one_eq_zero f

example (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 :=
  ModularForm.S2_Gamma0_2_eq_zero f

example (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) :
    CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f = 0 ↔
      (f : ℍ → ℂ) = 0 :=
  CuspForm.norm_eq_zero_iff _ f
