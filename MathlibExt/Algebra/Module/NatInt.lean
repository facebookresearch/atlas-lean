/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Module.NatInt

/-!
# Compatibility with integer module structures

The integer tower and commutation laws hold for arbitrary integer module
structures. The conclusions use the supplied scalar actions.
-/

@[expose] public section

namespace Module

universe u v

/-- The original ring action is compatible with any two supplied integer
module dictionaries on the ring and on its module. -/
theorem intModule_isScalarTower {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [dRM : Module R M]
    (dR : Module ℤ R) (dM : Module ℤ M) :
    @IsScalarTower ℤ R M dR.toSMul dRM.toSMul dM.toSMul := by
  refine @IsScalarTower.mk ℤ R M dR.toSMul dRM.toSMul dM.toSMul ?_
  intro z r m
  change dRM.smul (dR.smul z r) m = dM.smul z (dRM.smul r m)
  calc
    dRM.smul (dR.smul z r) m = dRM.smul (z • r) m :=
      congrArg (fun x : R => dRM.smul x m) (int_smul_eq_zsmul dR z r)
    _ = z • dRM.smul r m :=
      (@AddCommGroup.intIsScalarTower R M _ _ dRM).smul_assoc z r m
    _ = dM.smul z (dRM.smul r m) :=
      (int_smul_eq_zsmul dM z (dRM.smul r m)).symm

/-- A fixed distributive scalar action commutes with the actual supplied
integer module dictionary. The scalar type needs no multiplication. -/
theorem intModule_smulCommClass {S : Type u} {M : Type v}
    [AddCommGroup M] [dS : DistribSMul S M] [dM : Module ℤ M] :
    @SMulCommClass S ℤ M dS.toSMul dM.toSMul := by
  refine @SMulCommClass.mk S ℤ M dS.toSMul dM.toSMul ?_
  let : Module ℤ M := AddCommGroup.toIntModule M
  intro s z m
  change dS.smul s (dM.smul z m) = dM.smul z (dS.smul s m)
  calc
    dS.smul s (dM.smul z m) = dS.smul s (z • m) :=
      congrArg (fun x : M => dS.smul s x) (int_smul_eq_zsmul dM z m)
    _ = z • dS.smul s m := (DistribSMul.toAddMonoidHom M s).map_zsmul z m
    _ = dM.smul z (dS.smul s m) :=
      (int_smul_eq_zsmul dM z (dS.smul s m)).symm

end Module
