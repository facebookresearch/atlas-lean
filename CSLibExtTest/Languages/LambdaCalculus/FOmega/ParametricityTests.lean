/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.FOmega.Parametricity
import CSLibExt.Languages.LambdaCalculus.FOmega.ErasureSimulation
import CSLibExt.Languages.LambdaCalculus.FOmega.EmbeddingModel

/-! # Full higher-kind parametricity, conversion and model-bridge consumers -/

open Cslib.Languages.LambdaCalculus
open FOmega

private def opId {Δ : List Kind} : Ty Δ (.arrow .star .star) :=
  .lam (.var .zero)

private def poly {Δ : List Kind} : Ty Δ .star :=
  .all (κ := .star) (.arr (.var .zero) (.var .zero))

example {Δ : List Kind} {t : Tm Δ 0}
    (ht : Typing Fin.elim0 t higherIdType)
    (F : Ty Δ (.arrow .star .star)) (A : Ty Δ .star) (x : SystemF.Model) :
    SystemF.BetaEq
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t F) A)) x) x :=
  higher_kinded_identity ht F A x

example (x : SystemF.Model) :
    SystemF.BetaEq
      (SystemF.Model.app
        (Tm.eraseModel (.tapp (.tapp (higherId : Tm [] 0) opId) poly)) x) x :=
  higher_kinded_identity (higherId_typed Fin.elim0) opId poly x

example (x : SystemF.Model) :
    SystemF.BetaEq
      (SystemF.Model.app
        (Tm.eraseModel (.tapp (.tapp (higherId : Tm [] 0) opId) (.arr poly poly))) x) x :=
  higher_kinded_identity (higherId_typed Fin.elim0) opId (.arr poly poly) x

example {Δ : List Kind} (t : Tm Δ 0) :
    ¬ Typing Fin.elim0 t (.all (κ := .star) (.var .zero)) :=
  forall_var_uninhabited t

example {Δ : List Kind} (t : Tm Δ 0) :
    ¬ Typing Fin.elim0 t (.all (κ := .arrow .star .star)
      (.all (κ := .star) (.app (.var (.succ .zero)) (.var .zero)))) :=
  higher_result_uninhabited t

example {Δ : List Kind} {Γ : Ctx Δ 0} {t : Tm Δ 0} {A : Ty Δ .star}
    (ht : Typing Γ t A) (ρ : KEnv SystemF.Rel Δ) :
    (A.interpret ρ).holds (Tm.eraseModel t) (Tm.eraseModel t) :=
  fundamental_closed ht ρ

example {Δ : List Kind} {t : Tm Δ 0}
    (ht : Typing Fin.elim0 t higherIdType)
    (F G : Ty Δ (.arrow .star .star)) (A B : Ty Δ .star)
    (Φ : SystemF.Rel → SystemF.Rel) (R : SystemF.Rel)
    {x y : SystemF.Model} (hxy : (Φ R).holds x y) :
    (Φ R).holds
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t F) A)) x)
      (SystemF.Model.app (Tm.eraseModel (.tapp (.tapp t G) B)) y) :=
  higher_kinded_related ht F G A B Φ R hxy

private def env : KEnv SystemF.Rel [] := fun {_} x => nomatch x

private def convertedInstance : Tm [] 0 := .tapp (.tapp higherId opId) poly

private theorem convertedTyping : Typing Fin.elim0 convertedInstance (.arr poly poly) :=
  .conv (.tapp (.tapp (higherId_typed Fin.elim0))) (.arr (.beta _ _) (.beta _ _))

example {x y : SystemF.Model} (hxy : (poly.interpret env).holds x y) :
    (poly.interpret env).holds
      (SystemF.Model.app (Tm.eraseModel convertedInstance) x)
      (SystemF.Model.app (Tm.eraseModel convertedInstance) y) :=
  fundamental_closed convertedTyping env x y hxy
