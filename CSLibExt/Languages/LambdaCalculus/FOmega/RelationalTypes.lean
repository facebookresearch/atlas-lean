/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.FOmega.Conversion
public import CSLibExt.Languages.LambdaCalculus.SystemF.Relations

/-! # Higher-kinded relational interpretation of Fω types

The carrier is exactly System F's arbitrary beta-invariant binary relations.
At higher kinds it is the full function space over those carriers; universal
binders quantify all such kinded values. No new term model or relation is used.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.FOmega

/-- The generic kind algebra instantiated with the banked relation substrate. -/
def relationalAlgebra : KindAlgebra SystemF.Rel where
  arr := SystemF.Rel.arrow
  all := fun {_} => SystemF.Rel.universal

/-- A kinded type denotes a relation or an appropriately kinded function. -/
def Ty.interpret {Δ : List Kind} {κ : Kind} (t : Ty Δ κ)
    (ρ : KEnv SystemF.Rel Δ) : Kind.Sem SystemF.Rel κ :=
  t.eval relationalAlgebra ρ

namespace Ty

variable {Δ Ε : List Kind} {κ μ : Kind}

/-- Relational substitution at every kind, with arbitrary higher-kind values. -/
theorem interpret_subst (t : Ty Δ κ) (σ : Ty.Sub Δ Ε)
    (ρ : KEnv SystemF.Rel Ε) :
    (t.subst σ).interpret ρ =
      t.interpret (fun {_} x => (σ x).interpret ρ) :=
  eval_subst relationalAlgebra ρ σ t

/-- Proved type-beta conversion is sound for the higher-kinded relations. -/
theorem Conv.interpret {a b : Ty Δ κ} (h : Conv a b)
    (ρ : KEnv SystemF.Rel Δ) : a.interpret ρ = b.interpret ρ :=
  h.sound relationalAlgebra ρ

/-- Type renaming transports an arbitrary higher-kinded relation environment. -/
theorem interpret_rename (t : Ty Δ κ) (η : KRen Δ Ε)
    (ρ : KEnv SystemF.Rel Ε) :
    (t.rename η).interpret ρ = t.interpret (fun {_} x => ρ (η x)) :=
  eval_rename relationalAlgebra ρ η t

/-- A kinded type argument is interpreted before its universal is discharged. -/
theorem interpret_instantiate (b : Ty (μ :: Δ) κ) (a : Ty Δ μ)
    (ρ : KEnv SystemF.Rel Δ) :
    (b.instantiate a).interpret ρ =
      b.interpret (KEnv.extend ρ (a.interpret ρ)) :=
  eval_instantiate relationalAlgebra ρ b a

/-- A universal quantifies every semantic value of its bound kind. -/
@[simp] theorem interpret_all {b : Ty (κ :: Δ) .star}
    (ρ : KEnv SystemF.Rel Δ) (f g : SystemF.Model) :
    ((Ty.all b).interpret ρ).holds f g ↔
      ∀ R : Kind.Sem SystemF.Rel κ,
        (b.interpret (KEnv.extend ρ R)).holds f g := Iff.rfl

/-- An arrow relates every related pair of inputs at its codomain. -/
@[simp] theorem interpret_arr (a b : Ty Δ .star)
    (ρ : KEnv SystemF.Rel Δ) (f g : SystemF.Model) :
    ((Ty.arr a b).interpret ρ).holds f g ↔
      ∀ x y, (a.interpret ρ).holds x y →
        (b.interpret ρ).holds (SystemF.Model.app f x) (SystemF.Model.app g y) :=
  Iff.rfl

/-- Weakening ignores the arbitrary new semantic value, at every binder kind. -/
@[simp] theorem interpret_weaken (t : Ty Δ κ) (ρ : KEnv SystemF.Rel Δ)
    (R : Kind.Sem SystemF.Rel μ) :
    (t.rename KVar.succ).interpret (KEnv.extend ρ R) = t.interpret ρ :=
  interpret_rename t KVar.succ (KEnv.extend ρ R)

end Ty

end Cslib.Languages.LambdaCalculus.FOmega
