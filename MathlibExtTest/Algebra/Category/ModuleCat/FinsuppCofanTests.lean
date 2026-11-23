/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.FinsuppCofan

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

example (R : Type w) [Ring R] (M I : Type u) [AddCommGroup M] [Module R M] :
    IsColimit (ModuleCat.finsuppCofan R M I) := ModuleCat.finsuppCofanIsColimit R M I

example (R : Type w) [Ring R] (M I : Type u) [AddCommGroup M] [Module R M] (i : I) :
    (ModuleCat.finsuppCofan R M I).inj i =
      ModuleCat.ofHom (Finsupp.lsingle i (R := R) (M := M)) := rfl

example (R : Type w) [Ring R] (M I : Type u) [AddCommGroup M] [Module R M]
    (s : Cofan (fun _ : I => ModuleCat.of R M)) (i : I) (m : M) :
    ((ModuleCat.finsuppCofanIsColimit R M I).desc s).hom (Finsupp.single i m) =
      (s.inj i).hom m := by
  have h := (ModuleCat.finsuppCofanIsColimit R M I).fac s (Discrete.mk i)
  with_unfolding_all exact congrArg (fun f => f.hom m) h

#check @ModuleCat.finsuppCofan
#print axioms ModuleCat.finsuppCofan
#check @ModuleCat.finsuppCofanIsColimit
#print axioms ModuleCat.finsuppCofanIsColimit
