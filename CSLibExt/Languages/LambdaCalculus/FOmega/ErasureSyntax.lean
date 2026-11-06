/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Terms

/-! # Erasure adapter to the existing System F scoped syntax

This adapter is only for the existing System F untyped-model closing API, not
an assertion of System F typing. It drops both type term constructors and uses
a fixed closed annotation, which the model erases. There is no second untyped
syntax or relation carrier. The separately proved System F embedding has a
different, type-preserving direction.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega.Tm

/-- **Erasure of Fω terms to System F syntax.**
Erase types using the already banked System F scoped term carrier. -/
def eraseSyntax : {Δ : List Kind} → {m : Nat} → Tm Δ m → SystemF.Tm 0 m
  | _, _, .var i => .var i
  | _, _, .lam _ b => .lam (.all (.var 0)) (eraseSyntax b)
  | _, _, .app f a => .app (eraseSyntax f) (eraseSyntax a)
  | _, _, .tabs b => eraseSyntax b
  | _, _, .tapp f _ => eraseSyntax f

variable {Δ Ε : List Kind} {m k : Nat}

/-- **Fω erasure ignores type substitution.**
Erasure ignores all kind-correct type substitutions. -/
@[simp] theorem eraseSyntax_tySubst (σ : Ty.Sub Δ Ε) (t : Tm Δ m) :
    eraseSyntax (tySubst σ t) = eraseSyntax t := by
  induction t generalizing Ε with
  | var => rfl
  | lam A b ih => simp [eraseSyntax, ih]
  | app f a ihf iha => simp [eraseSyntax, ihf, iha]
  | tabs b ih => simp [eraseSyntax, ih]
  | tapp f A ih => simp [eraseSyntax, ih]

/-- **Fω erasure commutes with term-variable renaming.**
Erasure commutes with scoped term-variable renaming. -/
@[simp] theorem eraseSyntax_rename (ρ : Fin m → Fin k) (t : Tm Δ m) :
    eraseSyntax (rename ρ t) = SystemF.Tm.rename ρ (eraseSyntax t) := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih => simp [eraseSyntax, ih]
  | app f a ihf iha => simp [eraseSyntax, ihf, iha]
  | tabs b ih => simp [eraseSyntax, ih]
  | tapp f A ih => simp [eraseSyntax, ih]

private theorem eraseSyntax_liftSub (σ : Fin m → Tm Δ k)
    (i : Fin (m + 1)) :
    eraseSyntax (liftSub σ i) =
      SystemF.Tm.liftSub (fun j => eraseSyntax (σ j)) i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => simp [liftSub, SystemF.Tm.liftSub]

/-- **Fω erasure commutes with term substitution.**
Erasure commutes with simultaneous substitution of scoped terms. -/
@[simp] theorem eraseSyntax_subst (σ : Fin m → Tm Δ k) (t : Tm Δ m) :
    eraseSyntax (subst σ t) =
      SystemF.Tm.subst (fun i => eraseSyntax (σ i)) (eraseSyntax t) := by
  induction t generalizing k with
  | var => rfl
  | lam A b ih => simp [eraseSyntax, ih, eraseSyntax_liftSub]
  | app f a ihf iha => simp [eraseSyntax, ihf, iha]
  | tabs b ih => simp [eraseSyntax, ih, tyRename]
  | tapp f A ih => simp [eraseSyntax, ih]

/-- **Fω erasure commutes with term-binder instantiation.**
Erasure commutes with discharging a term binder. -/
@[simp] theorem eraseSyntax_instantiate (b : Tm Δ (m + 1)) (a : Tm Δ m) :
    eraseSyntax (instantiate b a) =
      SystemF.Tm.instantiate (eraseSyntax b) (eraseSyntax a) := by
  simp only [instantiate, eraseSyntax_subst, SystemF.Tm.instantiate]
  congr 1
  funext i
  induction i using Fin.cases <;> rfl

end Cslib.Languages.LambdaCalculus.FOmega.Tm
