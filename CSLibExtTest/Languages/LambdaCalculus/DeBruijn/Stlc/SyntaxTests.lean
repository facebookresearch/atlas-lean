/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax

/-!
# Consumer tests for the generic STLC renaming API

These examples exercise `Stlc.Tm.rename` directly: renaming beneath a lambda
leaves the bound variable fixed while shifting free variables, renaming
composes, and weakening shifts every free variable by one.
-/

open scoped CslibStlc

namespace Cslib.Languages.LambdaCalculus.Stlc

namespace SyntaxTests

/-- The single base type used in these examples. -/
abbrev b : Ty Unit := .base ()

/-- The identity function at `b`. -/
def idTm : Tm [] (b ⇒ b) := .lam (.var .zero)

/-- The constant function returning the unique free variable. -/
def constTm : Tm [b] (b ⇒ b) := .lam (.var (.succ .zero))

/-- Renaming by the identity is the identity on terms. -/
example : Tm.rename Var.id constTm = constTm := Tm.rename_id _

/-- Renaming beneath a lambda leaves the bound variable fixed. -/
example : (Tm.rename Var.succ idTm : Tm [b] (b ⇒ b)) = .lam (.var .zero) := rfl

/-- Renaming beneath a lambda shifts free variables. -/
example : (Tm.rename Var.succ constTm : Tm [b, b] (b ⇒ b)) = .lam (.var (.succ (.succ .zero))) := rfl

/-- Lifting preserves the bound variable and applies the renaming below it. -/
example (ρ : Ren [b] [b, b]) : Var.lift ρ (.zero : Var (b :: [b]) b) = .zero :=
  Var.lift_zero ρ

example (ρ : Ren [b] [b, b]) (x : Var [b] b) :
    Var.lift ρ (.succ x : Var (b :: [b]) b) = .succ (ρ x) :=
  Var.lift_succ ρ x

/-- Two successive weakenings shift a variable twice. -/
example : (Tm.rename Var.succ (Tm.rename Var.succ (.var .zero : Tm [b] b)) : Tm [b, b, b] b) =
    .var (.succ (.succ .zero)) := rfl

/-- Successive renamings agree with the composed renaming. -/
example (ρ : Ren [b] [b, b]) (σ : Ren [b, b] [b, b, b]) :
    Tm.rename σ (Tm.rename ρ constTm) = Tm.rename (Var.comp ρ σ) constTm :=
  Tm.rename_comp ρ σ constTm

/-- Weakening shifts the free variable of the constant function. -/
example : (Tm.weaken constTm : Tm [b, b] (b ⇒ b)) = .lam (.var (.succ (.succ .zero))) := rfl

/-- Weakening leaves a closed identity term unchanged in shape. -/
example : (Tm.weaken idTm : Tm [b] (b ⇒ b)) = .lam (.var .zero) := rfl

/-- Renaming distributes over application. -/
example (f : Tm [b] (b ⇒ b)) (a : Tm [b] b) :
    Tm.rename (Var.succ : Ren [b] [b, b]) (.app f a) =
      .app (Tm.rename (Var.succ : Ren [b] [b, b]) f) (Tm.rename (Var.succ : Ren [b] [b, b]) a) :=
  Tm.rename_app _ _ _

end SyntaxTests

end Cslib.Languages.LambdaCalculus.Stlc
