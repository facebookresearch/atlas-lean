/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Init
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Scoped pure System F

The two de Bruijn namespaces are separate. Index zero denotes the newest
variable. Types are impredicative: a universal type may be instantiated with
any type, including another universal type. Terms are scoped, not typed;
`Typing` in the next module is an independent five-rule judgment.

This project-authored presentation follows the pure calculus of Pierce,
*Types and Programming Languages*, Chapter 23. It has no subtyping, sums,
constants, recursion, or object-language universe hierarchy.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- **Scoped types of pure System F.** Pure System F types with `n` available type variables. -/
inductive Ty : Nat → Type where
  | var {n : Nat} : Fin n → Ty n
  | arr {n : Nat} : Ty n → Ty n → Ty n
  | all {n : Nat} : Ty (n + 1) → Ty n
  deriving DecidableEq, Repr

/-- **Lifting a scoped renaming under a binder.**
Extend a scoped renaming, preserving the newly bound variable. -/
def liftRen {n k : Nat} (ρ : Fin n → Fin k) :
    Fin (n + 1) → Fin (k + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

/-- **Lifted renaming fixes the newly bound variable.**
The new variable is unaffected by a lifted renaming. -/
@[simp] theorem liftRen_zero {n k : Nat} (ρ : Fin n → Fin k) :
    liftRen ρ 0 = 0 := rfl

/-- **Lifted renaming shifts each renamed old variable.**
A lifted renaming shifts every renamed old variable. -/
@[simp] theorem liftRen_succ {n k : Nat} (ρ : Fin n → Fin k)
    (i : Fin n) : liftRen ρ i.succ = (ρ i).succ := rfl

namespace Ty

/-- Capture-avoiding renaming of type variables. -/
@[simp] def rename {n k : Nat} (ρ : Fin n → Fin k) : Ty n → Ty k
  | .var i => .var (ρ i)
  | .arr A B => .arr (rename ρ A) (rename ρ B)
  | .all B => .all (rename (liftRen ρ) B)

/-- Lift a type substitution under one type binder. -/
def liftSub {n k : Nat} (σ : Fin n → Ty k) : Fin (n + 1) → Ty (k + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

/-- Simultaneous, capture-avoiding type substitution. -/
@[simp] def subst {n k : Nat} (σ : Fin n → Ty k) : Ty n → Ty k
  | .var i => σ i
  | .arr A B => .arr (subst σ A) (subst σ B)
  | .all B => .all (subst (liftSub σ) B)

/-- Discharge the newest type binder by an arbitrary type. -/
def instantiate {n : Nat} (B : Ty (n + 1)) (A : Ty n) : Ty n :=
  subst (Fin.cases A Ty.var) B

/-- **Lifted type substitution fixes the fresh variable.**
The fresh type variable is fixed by a lifted substitution. -/
@[simp] theorem liftSub_zero {n k : Nat} (σ : Fin n → Ty k) :
    liftSub σ 0 = .var 0 := rfl

/-- **Lifted type substitution weakens old images.**
Old type-substitution images are weakened under a binder. -/
@[simp] theorem liftSub_succ {n k : Nat} (σ : Fin n → Ty k)
    (i : Fin n) : liftSub σ i.succ = rename Fin.succ (σ i) := rfl

end Ty

/-- **Scoped terms of pure System F.** Pure terms with `n` type variables and `m` term variables. -/
inductive Tm : Nat → Nat → Type where
  | var {n m : Nat} : Fin m → Tm n m
  | lam {n m : Nat} : Ty n → Tm n (m + 1) → Tm n m
  | app {n m : Nat} : Tm n m → Tm n m → Tm n m
  | tabs {n m : Nat} : Tm (n + 1) m → Tm n m
  | tapp {n m : Nat} : Tm n m → Ty n → Tm n m
  deriving DecidableEq, Repr

/-- **Term variable contexts of System F.**
An ordered, unrestricted term context over `n` type variables. -/
abbrev Ctx (n m : Nat) := Fin m → Ty n

namespace Tm

/-- **Type substitution in System F terms.**
Substitute type variables in annotations, arguments, and type binders. -/
@[simp] def tySubst {n k m : Nat} (σ : Fin n → Ty k) : Tm n m → Tm k m
  | .var i => .var i
  | .lam A b => .lam (A.subst σ) (tySubst σ b)
  | .app f a => .app (tySubst σ f) (tySubst σ a)
  | .tabs b => .tabs (tySubst (Ty.liftSub σ) b)
  | .tapp f A => .tapp (tySubst σ f) (A.subst σ)

/-- **Term-variable renaming in System F terms.**
Rename term variables, lifting only at term binders. -/
@[simp] def rename {n m k : Nat} (ρ : Fin m → Fin k) : Tm n m → Tm n k
  | .var i => .var (ρ i)
  | .lam A b => .lam A (rename (liftRen ρ) b)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .tabs b => .tabs (rename ρ b)
  | .tapp f A => .tapp (rename ρ f) A

/-- **Type-variable renaming in System F terms.**
Rename type variables without changing term variables. -/
def tyRename {n k m : Nat} (ρ : Fin n → Fin k) (t : Tm n m) : Tm k m :=
  tySubst (fun i => .var (ρ i)) t

/-- **Lifting a term substitution under a term lambda.**
Lift a simultaneous term substitution beneath a term lambda. -/
def liftSub {n m k : Nat} (σ : Fin m → Tm n k) :
    Fin (m + 1) → Tm n (k + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

/-- **Simultaneous term substitution in System F terms.**
Simultaneous term substitution, avoiding both sorts of capture. -/
@[simp] def subst {n m k : Nat} (σ : Fin m → Tm n k) : Tm n m → Tm n k
  | .var i => σ i
  | .lam A b => .lam A (subst (liftSub σ) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .tabs b => .tabs (subst (fun i => tyRename Fin.succ (σ i)) b)
  | .tapp f A => .tapp (subst σ f) A

/-- **Instantiating the newest term binder of a term.**
Replace the newest term variable and discharge its binder. -/
def instantiate {n m : Nat} (b : Tm n (m + 1)) (a : Tm n m) : Tm n m :=
  subst (Fin.cases a Tm.var) b

end Tm

end Cslib.Languages.LambdaCalculus.SystemF
