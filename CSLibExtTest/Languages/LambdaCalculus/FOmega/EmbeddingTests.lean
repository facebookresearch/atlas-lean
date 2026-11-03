/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.FOmega.Embedding
import CSLibExt.Languages.LambdaCalculus.FOmega.ErasureSyntax

/-! # Nested System F embedding, simulation and erasure-binding probes -/

open Cslib.Languages.LambdaCalculus.FOmega

private def sourceType : Cslib.Languages.LambdaCalculus.SystemF.Ty 0 :=
  .all (.arr (.var 0) (.all (.arr (.var 1) (.var 1))))

private def sourceTerm : Cslib.Languages.LambdaCalculus.SystemF.Tm 0 0 :=
  .tabs (.lam (.var 0) (.tabs (.lam (.var 1) (.var 1))))

private theorem sourceTyping :
    Cslib.Languages.LambdaCalculus.SystemF.Typing Fin.elim0 sourceTerm sourceType :=
  .tabs (.lam (.tabs (.lam (.var 1))))

example : Ty.embed sourceType =
    .all (κ := .star) (.arr (.var .zero)
      (.all (κ := .star) (.arr (.var (.succ .zero)) (.var (.succ .zero))))) := rfl

example : Typing (fun i => Ty.embed (Fin.elim0 i))
    (Tm.embed sourceTerm) (Ty.embed sourceType) := Tm.embed_typing sourceTyping

example : Step
    (Tm.embed (.tapp sourceTerm sourceType))
    (Tm.embed (.lam sourceType (.tabs (.lam (sourceType.rename Fin.succ) (.var 1))))) :=
  Tm.embed_step .tyBeta

example : Tm.eraseSyntax (Tm.embed sourceTerm) =
    .lam (.all (.var 0)) (.lam (.all (.var 0)) (.var 1)) := rfl

example {Δ : List Kind} {m : Nat} {κ : Kind}
    (b : Tm (κ :: Δ) m) (A : Ty Δ κ) :
    Tm.eraseSyntax (.tapp (.tabs b) A) =
      Tm.eraseSyntax (b.tySubst (Ty.single A)) :=
  (Tm.eraseSyntax_tySubst (Ty.single A) b).symm

example {Δ : List Kind} {m k : Nat} (σ : Fin m → Tm Δ k) (t : Tm Δ m) :
    Tm.eraseSyntax (t.subst σ) =
      Cslib.Languages.LambdaCalculus.SystemF.Tm.subst
        (fun i => Tm.eraseSyntax (σ i)) (Tm.eraseSyntax t) :=
  Tm.eraseSyntax_subst σ t
