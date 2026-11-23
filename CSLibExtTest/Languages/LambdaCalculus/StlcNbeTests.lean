/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Nbe

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.NbeTests

open scoped CslibStlc

abbrev Atom := Ty.base (Base := Unit) ()

/-- Reifying a reflected base neutral returns the corresponding base normal
form. -/
example : quote Atom (reflect Atom (.var (.zero : Var [Atom] Atom))) =
    .base (.var .zero) := rfl

/-- Reflected functions are eta-expanded during reification. -/
example :
    quote (Atom ⇒ Atom)
        (reflect (Atom ⇒ Atom) (.var (.zero : Var [Atom ⇒ Atom] (Atom ⇒ Atom)))) =
      .lam (.base (.app (.var (.succ .zero)) (.base (.var .zero)))) := rfl

/-- Reification of a reflected higher-order neutral introduces one lambda per
arrow in the result type. -/
example :
    quote (Atom ⇒ Atom ⇒ Atom)
        (reflect (Atom ⇒ Atom ⇒ Atom)
          (.var (.zero : Var [Atom ⇒ Atom ⇒ Atom] (Atom ⇒ Atom ⇒ Atom)))) =
      .lam (.lam (.base (.app
        (.app (.var (.succ (.succ .zero))) (.base (.var (.succ .zero))))
        (.base (.var .zero))))) := rfl

/-- Renaming under a binder preserves the bound variable and renames the free
variable. -/
example :
    let n : Nf [Atom] (Atom ⇒ Atom) := .lam (.base (.var (.succ .zero)))
    let ρ : Ren [Atom] [Atom, Atom] := fun x => .succ x
    n.rename ρ =
      (.lam (.base (.var (.succ (.succ .zero)))) : Nf [Atom, Atom] (Atom ⇒ Atom)) := by
  rfl

/-- Neutral and normal-form renaming form an identity action. -/
example (n : Ne [Atom] Atom) : n.rename Var.id = n := Ne.rename_id n

example (n : Nf [Atom] Atom) : n.rename Var.id = n := Nf.rename_id n

/-- Successive normal-form renamings compose. -/
example (n : Nf [Atom] Atom) (ρ : Ren [Atom] [Atom, Atom])
    (σ : Ren [Atom, Atom] [Atom, Atom, Atom]) :
    (n.rename ρ).rename σ = n.rename (Var.comp ρ σ) := Nf.rename_comp ρ σ n

/-- Forgetting the normal-form invariant commutes with renaming. -/
example (n : Nf [Atom] Atom) (ρ : Ren [Atom] [Atom, Atom]) :
    (n.rename ρ).toTm = Tm.rename ρ n.toTm := Nf.toTm_rename ρ n

/-- Extending a semantic environment maps zero to the new value and successors
through the old environment. -/
example (a : Sem [Atom] Atom) (η : SemEnv [Atom] [Atom]) :
    SemEnv.cons a η (.zero : Var [Atom, Atom] Atom) = a := rfl

example (a : Sem [Atom] Atom) (η : SemEnv [Atom] [Atom]) :
    SemEnv.cons a η (.succ .zero : Var [Atom, Atom] Atom) = η .zero := rfl

/-- Renaming a semantic function composes its future-context renaming before
application. -/
example (f : Sem [Atom] (Atom ⇒ Atom)) (ρ : Ren [Atom] [Atom, Atom])
    (σ : Ren [Atom, Atom] [Atom, Atom, Atom]) (a : Sem [Atom, Atom, Atom] Atom) :
    Sem.rename ρ (Atom ⇒ Atom) f σ a = f (Var.comp ρ σ) a := rfl

/-- Semantic-environment renaming is an identity action and composes. -/
example (η : SemEnv [Atom] [Atom ⇒ Atom]) :
    @SemEnv.rename Unit [Atom ⇒ Atom] [Atom] [Atom] Var.id η = @η :=
  SemEnv.rename_id η

example (η : SemEnv [Atom] [Atom ⇒ Atom]) (ρ : Ren [Atom] [Atom, Atom])
    (σ : Ren [Atom, Atom] [Atom, Atom, Atom]) :
    @SemEnv.rename Unit [Atom ⇒ Atom] [Atom, Atom] [Atom, Atom, Atom] σ
        (@SemEnv.rename Unit [Atom ⇒ Atom] [Atom] [Atom, Atom] ρ η) =
      @SemEnv.rename Unit [Atom ⇒ Atom] [Atom] [Atom, Atom, Atom]
        (Var.comp ρ σ) η := SemEnv.rename_comp ρ σ η

#print axioms Ne.rename
#print axioms Nf.rename
#print axioms reflect
#print axioms quote

end Cslib.Languages.LambdaCalculus.Stlc.NbeTests
