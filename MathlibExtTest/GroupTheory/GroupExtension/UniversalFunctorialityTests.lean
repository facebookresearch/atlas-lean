/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.GroupTheory.GroupExtension.UniversalFunctoriality
import MathlibExt.GroupTheory.GroupExtension.UniversalRecognition
import MathlibExt.KTheory.Ring.K2.StableSteinbergUniversal
import Batteries.Tactic.Lint

/-!
# Original-map clients of canonical universal lifts

Independent kernel, total and quotient universes are exercised through the
whole original extension squares and their kernel maps. The unchanged
recognition and stable Steinberg statements remain ordinary regression imports.
-/

set_option autoImplicit false

noncomputable section

universe uN uE uG vN vE vG

open GroupExtension

namespace MathlibExtTest.UniversalFunctoriality

variable {N : Type uN} {E : Type uE} {G : Type uG}
variable {K : Type vN} {D : Type vE} {H : Type vG}
variable [Group N] [Group E] [Group G] [Group K] [Group D] [Group H]
variable (S : GroupExtension N E G) (T : GroupExtension K D H)

example : IsUniversalFor.{uN, uE, uG, uN, uE} S ↔ S.IsUniversal := Iff.rfl

example (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (hT : T.IsCentral) (f : G →* H) :
    (hS.liftHom T hT f).totalHom.comp S.inl =
      T.inl.comp (hS.liftHom T hT f).kernelHom :=
  (hS.liftHom T hT f).inl_comm

example (hS : IsUniversalFor.{uN, uE, uG, vN, max uG vE} S)
    (hT : T.IsCentral) (f : G →* H) (n : N) :
    hS.lift T hT f (S.inl n) = T.inl ((hS.liftHom T hT f).kernelHom n) :=
  Hom.inl_comm_apply (hS.liftHom T hT f) n

example (hS : IsUniversalFor.{uN, uE, uG, uN, max uG uE} S) :
    (hS.liftHom S hS.1 (MonoidHom.id G)).kernelHom = MonoidHom.id N :=
  hS.liftHom_kernelHom_id

#check @GroupExtension.IsCentral.isUniversal_of_splits
#check @AlgebraicKTheory.StableSteinberg.steinbergExtension_isUniversal
#print axioms GroupExtension.IsUniversalFor.lift_unique
#print axioms GroupExtension.IsUniversalFor.liftHom_comp
#print axioms GroupExtension.IsUniversalFor.liftHom_kernelHom_comp

#lint only unusedArguments in MathlibExt.GroupTheory.CentralExtension
#lint only unusedArguments in MathlibExt.GroupTheory.GroupExtension.UniversalFunctoriality

end MathlibExtTest.UniversalFunctoriality
