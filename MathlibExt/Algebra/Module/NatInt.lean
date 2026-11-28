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
# Integer scalars and arbitrary module actions

Let R be a ring and M an R-module, with their carriers in independent
universes u and v. For any integer-module structures on the additive groups
of R and M, the R-action satisfies (z • r) • m = z • (r • m).
Each integer action is repeated addition with its extension to negative integers.

More generally, if a type S acts distributively on an additive commutative
group M, that action commutes with any integer-module structure on M:
s • (z • m) = z • (s • m). No multiplication on S is required.
-/

@[expose] public section

namespace Module

universe u v

/-- Let R be a ring, M an R-module, and let d_R and d_M be any
integer-module structures on their additive groups. The R-action and these
integer actions form a scalar tower: for z ∈ ℤ, r ∈ R and m ∈ M,
(d_R(z, r)) • m = d_M(z, r • m). The ring and module carriers may lie in
independent universes. -/
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

/-- Let S be a type acting distributively on an additive commutative
group M, and give M any integer-module structure. Then the S-action
commutes with integer multiplication:
s • (z • m) = z • (s • m) for s ∈ S, z ∈ ℤ and m ∈ M.
No monoid or ring structure on S is assumed. -/
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
