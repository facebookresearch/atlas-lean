/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.EffectHandlers.Substitution

/-!
# Tests for renaming, weakening and substitution in the effect-handler calculus

Statement pins restate every public declaration of
`CSLibExt.Languages.LambdaCalculus.EffectHandlers.Substitution` and are closed by the declaration
itself, so a weakened or drifted statement fails here; the packaging operations of the
structural-typing instance are pinned by their defining equations.

Concrete checks, on a local signature with one operation `flip : bool → bool`:
* single and double instantiation on terms, and the lemmas applied to them, including the
  instantiated operation clause of a handler rule;
* weakening shifts free variables;
* the structural-typing instance applied to a clause body, through both of its fields;
* the instance has content: the value branch of the binder and of instantiation, and the shift of
  weakening, cannot be replaced by no-ops, while the computation branches are the identity.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.EffectHandlers

namespace SubstitutionTests

universe u

/-! ### Statement pins -/

section Pins

variable {Op : Type u} [DecidableEq Op] {sig : Op → VTy Op × VTy Op}

/-- Pin: renaming preserves the typing of values. -/
theorem HasVTy.ren_pin :
    ∀ {Γ Γ' : List (VTy Op)} {v : Val Op} {A : VTy Op}, HasVTy sig Γ v A →
      ∀ {ρ : ℕ → ℕ}, (∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) →
        HasVTy sig Γ' (v.ren ρ) A :=
  @HasVTy.ren Op _ sig

/-- Pin: renaming preserves the typing of computations. -/
theorem HasCTy.ren_pin :
    ∀ {Γ Γ' : List (VTy Op)} {c : Comp Op} {C : CTy Op}, HasCTy sig Γ c C →
      ∀ {ρ : ℕ → ℕ}, (∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) →
        HasCTy sig Γ' (c.ren ρ) C :=
  @HasCTy.ren Op _ sig

/-- Pin: renaming preserves the typing of operation clauses. -/
theorem HasClauses.ren_pin :
    ∀ {Γ Γ' : List (VTy Op)} {cls : List (Op × Comp Op)} {B : VTy Op} {Δ' : Finset Op},
      HasClauses sig Γ cls B Δ' →
      ∀ {ρ : ℕ → ℕ}, (∀ i T, Γ[i]? = some T → Γ'[ρ i]? = some T) →
        HasClauses sig Γ' (Clauses.ren ρ cls) B Δ' :=
  @HasClauses.ren Op _ sig

/-- Pin: weakening for values. -/
theorem HasVTy.weaken_pin :
    ∀ {Γ : List (VTy Op)} {v : Val Op} {A : VTy Op} (Θ : List (VTy Op)),
      HasVTy sig Γ v A → HasVTy sig (Θ ++ Γ) (v.ren (· + Θ.length)) A :=
  @HasVTy.weaken Op _ sig

/-- Pin: weakening for computations. -/
theorem HasCTy.weaken_pin :
    ∀ {Γ : List (VTy Op)} {c : Comp Op} {C : CTy Op} (Θ : List (VTy Op)),
      HasCTy sig Γ c C → HasCTy sig (Θ ++ Γ) (c.ren (· + Θ.length)) C :=
  @HasCTy.weaken Op _ sig

/-- Pin: parallel substitution preserves the typing of values. -/
theorem HasVTy.subst_pin :
    ∀ {Γ Γ' : List (VTy Op)} {v : Val Op} {A : VTy Op}, HasVTy sig Γ v A →
      ∀ {σ : ℕ → Val Op}, (∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) →
        HasVTy sig Γ' (v.subst σ) A :=
  @HasVTy.subst Op _ sig

/-- Pin: parallel substitution preserves the typing of computations. -/
theorem HasCTy.subst_pin :
    ∀ {Γ Γ' : List (VTy Op)} {c : Comp Op} {C : CTy Op}, HasCTy sig Γ c C →
      ∀ {σ : ℕ → Val Op}, (∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) →
        HasCTy sig Γ' (c.subst σ) C :=
  @HasCTy.subst Op _ sig

/-- Pin: parallel substitution preserves the typing of operation clauses. -/
theorem HasClauses.subst_pin :
    ∀ {Γ Γ' : List (VTy Op)} {cls : List (Op × Comp Op)} {B : VTy Op} {Δ' : Finset Op},
      HasClauses sig Γ cls B Δ' →
      ∀ {σ : ℕ → Val Op}, (∀ i T, Γ[i]? = some T → HasVTy sig Γ' (σ i) T) →
        HasClauses sig Γ' (Clauses.subst σ cls) B Δ' :=
  @HasClauses.subst Op _ sig

/-- Pin: single instantiation for values. -/
theorem HasVTy.inst_pin :
    ∀ {Γ : List (VTy Op)} {w v : Val Op} {A B : VTy Op},
      HasVTy sig (A :: Γ) w B → HasVTy sig Γ v A → HasVTy sig Γ (w.inst v) B :=
  @HasVTy.inst Op _ sig

/-- Pin: single instantiation for computations. -/
theorem HasCTy.inst_pin :
    ∀ {Γ : List (VTy Op)} {c : Comp Op} {v : Val Op} {A : VTy Op} {C : CTy Op},
      HasCTy sig (A :: Γ) c C → HasVTy sig Γ v A → HasCTy sig Γ (c.inst v) C :=
  @HasCTy.inst Op _ sig

/-- Pin: double instantiation. -/
theorem HasCTy.inst₂_pin :
    ∀ {Γ : List (VTy Op)} {c : Comp Op} {x k : Val Op} {A K : VTy Op} {C : CTy Op},
      HasCTy sig (K :: A :: Γ) c C → HasVTy sig Γ x A → HasVTy sig Γ k K →
        HasCTy sig Γ (c.inst₂ x k) C :=
  @HasCTy.inst₂ Op _ sig

/-- Pin: packaged typing. -/
theorem HasT_pin (Γ : List (VTy Op)) (v : Val Op) (c : Comp Op) (A : VTy Op) (C : CTy Op) :
    (HasT sig Γ (.inl v) (.inl A) ↔ HasVTy sig Γ v A) ∧
    (HasT sig Γ (.inr c) (.inr C) ↔ HasCTy sig Γ c C) ∧
    (HasT sig Γ (.inl v) (.inr C) ↔ False) ∧ (HasT sig Γ (.inr c) (.inl A) ↔ False) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Pin: the structural-typing instance, with its data. -/
theorem structuralTyping_pin :
    TypeSafety.StructuralTyping (HasT sig) bindT instT (fun Γ Γ' => ∃ Θ, Γ' = Θ ++ Γ) wkT :=
  structuralTyping

end Pins

section PackagingPins

variable {Op : Type u}

/-- Pin: binding at a value type adds an innermost variable; at a computation type it binds
nothing. -/
theorem bindT_pin (Γ : List (VTy Op)) (A : VTy Op) (C : CTy Op) :
    bindT Γ () (.inl A) = A :: Γ ∧ bindT Γ () (.inr C) = Γ :=
  ⟨rfl, rfl⟩

/-- Pin: instantiating by a value substitutes it; instantiating by a computation is the
identity. -/
theorem instT_pin (w v : Val Op) (c c' : Comp Op) (e : Val Op ⊕ Comp Op) :
    instT (.inl w) () (.inl v) = .inl (w.inst v) ∧ instT (.inr c) () (.inl v) = .inr (c.inst v) ∧
    instT e () (.inr c') = e :=
  ⟨rfl, rfl, by cases e <;> rfl⟩

/-- Pin: weakening shifts by the difference of the context lengths. -/
theorem wkT_pin (Γ Γ' : List (VTy Op)) (v : Val Op) (c : Comp Op) :
    wkT Γ Γ' (.inl v) = .inl (v.ren (· + (Γ'.length - Γ.length))) ∧
    wkT Γ Γ' (.inr c) = .inr (c.ren (· + (Γ'.length - Γ.length))) :=
  ⟨rfl, rfl⟩

end PackagingPins

/-! ### A local signature -/

/-- A single operation `flip : bool → bool`. -/
inductive Fl where
  /-- The operation. -/
  | flip : Fl
  deriving DecidableEq

/-- The signature: `flip : bool → bool`. -/
def flSig : Fl → VTy Fl × VTy Fl
  | .flip => (.bool, .bool)

/-- `if x then flip false else return x`, with `x` the innermost variable. -/
def body : Comp Fl :=
  .ite (.var 0) (.op .flip .ff) (.ret (.var 0))

theorem body_typed : HasCTy flSig [.bool] body ⟨.bool, {.flip}⟩ :=
  .ite (.var rfl) (.op (by decide) .ff) (.ret (.var rfl))

/-! ### Instantiation and weakening on terms -/

theorem body_inst : body.inst .tt = .ite .tt (.op .flip .ff) (.ret .tt) :=
  rfl

theorem body_inst_typed : HasCTy flSig [] (body.inst .tt) ⟨.bool, {.flip}⟩ :=
  HasCTy.inst body_typed .tt

/-- Instantiating a value under a binder raises the free variables of the argument. -/
theorem lam_inst : (Val.lam (.ret (.var 1)) : Val Fl).inst (.var 3) = .lam (.ret (.var 4)) :=
  rfl

theorem lam_inst_typed :
    HasVTy flSig [.unit, .unit, .unit, .bool] ((Val.lam (.ret (.var 1))).inst (.var 3))
      (.fn .unit .bool ∅) :=
  HasVTy.inst (.lam (.ret (.var rfl))) (.var rfl)

/-- The operation clause `flip(x; k) ↦ k x`. -/
def clause : Comp Fl :=
  .app (.var 0) (.var 1)

/-- Double instantiation replaces the continuation (index `0`) and the parameter (index `1`). -/
theorem clause_inst₂ (κ : Val Fl) : clause.inst₂ .tt κ = .app κ .tt :=
  rfl

/-- The instantiated clause of a handler rule is typed: with `k : bool → bool ! ∅` and
`x : bool`. -/
theorem clause_inst₂_typed :
    HasCTy flSig [] (clause.inst₂ .tt (.lam (.ret (.var 0)))) ⟨.bool, ∅⟩ :=
  HasCTy.inst₂ (.app (.var rfl) (.var rfl)) .tt (.lam (.ret (.var rfl)))

/-- Weakening by a block of two variables shifts every free variable by two. -/
theorem body_weaken :
    HasCTy flSig [.unit, .unit, .bool] (.ite (.var 2) (.op .flip .ff) (.ret (.var 2)))
      ⟨.bool, {.flip}⟩ :=
  HasCTy.weaken [.unit, .unit] body_typed

/-- A renaming that swaps the two innermost variables. -/
theorem ren_swap :
    HasVTy flSig [.bool, .unit] ((Val.var 0 : Val Fl).ren fun | 0 => 1 | 1 => 0 | i => i)
      .unit :=
  HasVTy.ren (Γ := [.unit, .bool]) (.var rfl) fun i T h => by
    match i, h with
    | 0, h => exact h
    | 1, h => exact h

/-- Substitution into clauses keeps their labels and types their bodies. -/
theorem clauses_subst_typed :
    HasClauses flSig [] (Clauses.subst (fun _ => .tt) [(.flip, clause)]) .bool ∅ :=
  HasClauses.subst (Γ := []) (.cons (.app (.var rfl) (.var rfl)) .nil) fun _ _ h => by
    simp at h

theorem clauses_ren_typed :
    HasClauses flSig [.unit] (Clauses.ren (· + 1) [(.flip, clause)]) .bool ∅ :=
  HasClauses.ren (Γ := []) (.cons (.app (.var rfl) (.var rfl)) .nil) fun _ _ h => by
    simp at h

/-! ### T9: the structural-typing instance on a clause body -/

/-- Substitution through the interface, at a value binder: `x : bool ⊢ body` and `⊢ true : bool`
give `⊢ body[true/x]`. -/
theorem structural_subst_example :
    HasT flSig [] (.inr (.ite .tt (.op .flip .ff) (.ret .tt))) (.inr ⟨.bool, {.flip}⟩) :=
  structuralTyping.subst (Γ := []) (x := ()) (A := .inl .bool) (e := .inr body)
    (v := .inl .tt) body_typed .tt

/-- Substitution through the interface into the operation clause `flip(x; k) ↦ k x`: the
continuation (index `0`) is instantiated by `fun y ↦ return y`, and the parameter moves from
index `1` to index `0`. -/
theorem structural_subst_clause :
    HasT flSig [.bool] (.inr (.app (.lam (.ret (.var 0))) (.var 0))) (.inr ⟨.bool, ∅⟩) :=
  structuralTyping.subst (Γ := [.bool]) (x := ()) (A := .inl (.fn .bool .bool ∅))
    (e := .inr clause) (v := .inl (.lam (.ret (.var 0)))) (B := .inr ⟨.bool, ∅⟩)
    (HasCTy.app (HasVTy.var rfl) (HasVTy.var rfl)) (HasVTy.lam (HasCTy.ret (HasVTy.var rfl)))

/-- Weakening through the interface shifts: adding `unit` innermost turns variable `0` into
variable `1`. -/
theorem structural_weaken_example :
    HasT flSig [.unit, .bool] (.inl (.var 1)) (.inl .bool) :=
  structuralTyping.weaken (Γ := [.bool]) (Δ := [.unit, .bool]) (t := .inl (.var 0))
    ⟨[.unit], rfl⟩ (HasVTy.var rfl)

/-- At a computation binder the context is unchanged and instantiation is the identity. -/
theorem structural_subst_computation_binder :
    HasT flSig [.bool] (.inr body) (.inr ⟨.bool, {.flip}⟩) :=
  structuralTyping.subst (Γ := [.bool]) (x := ()) (A := .inr ⟨.bool, ∅⟩) (e := .inr body)
    (v := .inr (.ret .ff)) body_typed (HasCTy.ret .ff)

/-! ### The instance has content -/

/-- **The value branch of instantiation has content**: an instantiation that drops its value
argument fails the interface. -/
theorem dropped_value_instantiation_fails :
    ¬ TypeSafety.StructuralTyping (HasT flSig) bindT (fun e _ _ => e)
      (fun Γ Γ' => ∃ Θ, Γ' = Θ ++ Γ) wkT := by
  intro h
  have h' : HasT flSig [] (.inl (.var 0)) (.inl .bool) :=
    h.subst (Γ := []) (x := ()) (A := .inl .bool) (e := .inl (.var 0)) (v := .inl .tt)
      (HasVTy.var rfl) HasVTy.tt
  cases h' with
  | var hx => simp at hx

/-- **The value branch of the binder has content**: a binder that ignores value types fails the
interface. -/
theorem no_op_value_binder_fails :
    ¬ TypeSafety.StructuralTyping (HasT flSig) (fun Γ _ _ => Γ) instT
      (fun Γ Γ' => ∃ Θ, Γ' = Θ ++ Γ) wkT := by
  intro h
  have h' : HasT flSig [.bool] (.inl .unit) (.inl .bool) :=
    h.subst (Γ := [.bool]) (x := ()) (A := .inl .unit) (e := .inl (.var 0)) (v := .inl .unit)
      (HasVTy.var rfl) HasVTy.unit
  cases h'

/-- **Weakening needs its shift**: with the identity action, weakening fails. -/
theorem identity_wk_fails :
    ¬ TypeSafety.StructuralTyping (HasT flSig) bindT instT (fun Γ Γ' => ∃ Θ, Γ' = Θ ++ Γ)
      (fun _ _ t => t) := by
  intro h
  have h' : HasT flSig [.unit, .bool] (.inl (.var 0)) (.inl .bool) :=
    h.weaken (Γ := [.bool]) (Δ := [.unit, .bool]) (t := .inl (.var 0)) ⟨[.unit], rfl⟩
      (HasVTy.var rfl)
  cases h' with
  | var hx => simp at hx

end SubstitutionTests

end Cslib.Languages.LambdaCalculus.EffectHandlers
