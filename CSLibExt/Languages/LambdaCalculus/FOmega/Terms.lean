/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Syntax
public import CSLibExt.Languages.LambdaCalculus.SystemF.Syntax

/-! # Scoped pure Fω terms

There are separate term and kinded-type namespaces. The finite term-variable
lifting primitive is reused from the same-project System F syntax; type binders
instead extend the kind telescope. Terms are scoped, not intrinsically typed.

The binding equations adapt the same-project System F syntax interface in
`CSLibExt/Languages/LambdaCalculus/SystemF/Syntax.lean` to kind-indexed
operators.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- **Scoped pure Fω terms.** Pure terms at a kind telescope and a finite term-variable depth. -/
inductive Tm : List Kind → Nat → Type where
  | var {Δ : List Kind} {m : Nat} : Fin m → Tm Δ m
  | lam {Δ : List Kind} {m : Nat} : Ty Δ .star → Tm Δ (m + 1) → Tm Δ m
  | app {Δ : List Kind} {m : Nat} : Tm Δ m → Tm Δ m → Tm Δ m
  | tabs {Δ : List Kind} {m : Nat} {κ : Kind} : Tm (κ :: Δ) m → Tm Δ m
  | tapp {Δ : List Kind} {m : Nat} {κ : Kind} : Tm Δ m → Ty Δ κ → Tm Δ m

/-- **Term contexts of pure Fω.** An ordered unrestricted term context of kind-`star` types. -/
abbrev Ctx (Δ : List Kind) (m : Nat) := Fin m → Ty Δ .star

namespace Tm

/-- **Type substitution in Fω terms.**
Substitute kinded type variables in all annotations and type arguments. -/
@[simp] def tySubst {Δ Ε : List Kind} {m : Nat} (σ : Ty.Sub Δ Ε) :
    Tm Δ m → Tm Ε m
  | .var i => .var i
  | .lam A b => .lam (A.subst σ) (tySubst σ b)
  | .app f a => .app (tySubst σ f) (tySubst σ a)
  | .tabs b => .tabs (tySubst (Ty.liftSub σ) b)
  | .tapp f A => .tapp (tySubst σ f) (A.subst σ)

/-- **Type-variable renaming in Fω terms.**
Rename type variables without changing term variables. -/
def tyRename {Δ Ε : List Kind} {m : Nat} (ρ : KRen Δ Ε) (t : Tm Δ m) :
    Tm Ε m := tySubst (fun {_} x => .var (ρ x)) t

/-- **Term-variable renaming in Fω terms.**
Rename term variables, lifting only beneath term lambdas. -/
@[simp] def rename {Δ : List Kind} {m k : Nat} (ρ : Fin m → Fin k) :
    Tm Δ m → Tm Δ k
  | .var i => .var (ρ i)
  | .lam A b => .lam A (rename (SystemF.liftRen ρ) b)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tabs b => .tabs (rename ρ b)
  | .tapp f A => .tapp (rename ρ f) A

/-- **Lifting a term substitution under a term binder.**
Lift a term substitution beneath one term binder. -/
def liftSub {Δ : List Kind} {m k : Nat} (σ : Fin m → Tm Δ k) :
    Fin (m + 1) → Tm Δ (k + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

/-- **Simultaneous term substitution in Fω.**
Term substitution avoids capture in both namespaces. -/
@[simp] def subst {Δ : List Kind} {m k : Nat} (σ : Fin m → Tm Δ k) :
    Tm Δ m → Tm Δ k
  | .var i => σ i
  | .lam A b => .lam A (subst (liftSub σ) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .tabs b => .tabs (subst (fun i => tyRename KVar.succ (σ i)) b)
  | .tapp f A => .tapp (subst σ f) A

/-- **Instantiation of an Fω term binder.** Discharge the newest term binder. -/
def instantiate {Δ : List Kind} {m : Nat} (b : Tm Δ (m + 1))
    (a : Tm Δ m) : Tm Δ m := subst (Fin.cases a Tm.var) b

end Tm

end Cslib.Languages.LambdaCalculus.FOmega
