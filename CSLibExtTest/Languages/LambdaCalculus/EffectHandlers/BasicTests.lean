/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.EffectHandlers.Basic
public import Cslib.Foundations.Relation.Defs

/-!
# Tests for the effect-handler calculus: syntax, typing and semantics

Pins restate every public declaration of `CSLibExt.Languages.LambdaCalculus.EffectHandlers.Basic`:
the constructors of the syntax and context types (with exhaustive matches, so a constructor
cannot be added or dropped silently), the defining equations of every operation, and every rule
of the typing judgments and of the step relation, each closed by the declaration itself.

Concrete checks, on local operation signatures:
* a boolean state handler in the style of Pretnar 2015, §2, typed on a program that reads and
  writes the state;
* an operation outside the effect set is ill-typed;
* a handler that neither handles nor forwards an operation is ill-typed, and is typable once the
  operation is forwarded;
* a handler may change the result type through its return clause, while a clause that uses its
  continuation at another answer type is ill-typed;
* deep handling: both calls of a two-call program are caught, through the re-installed handler;
* handler-delimited contexts: of two nested handlers for an operation only the inner one fires,
  and an operation the inner handler does not handle is caught by the outer one in one step, with
  no forwarding step;
* handler frames are handler literals: under a handler given by a variable no step is taken and
  no outer handler catches the call, and substituting a handler literal for the variable then
  lets the inner handler catch it;
* answers: returned values and uncaught calls are answers and normal forms, a caught call is not
  an answer, and neither is a call under a variable or under `()` in handler position, while an
  uncaught call under a handler literal is;
* Pretnar's typing rule for `op(v; y. c)` is derivable for `do y ← op o v in c`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.EffectHandlers

namespace BasicTests

universe u

/-! ### Pins: syntax -/

section SyntaxPins

variable {Op : Type u}

/-- Pin: the value types and their constructors. -/
example : VTy Op × VTy Op × (VTy Op → VTy Op → Finset Op → VTy Op) ×
    (VTy Op → Finset Op → VTy Op → Finset Op → VTy Op) :=
  (.unit, .bool, .fn, .hand)

/-- Pin: `VTy` has exactly these constructors. -/
def vtyTag : VTy Op → ℕ
  | .unit => 0
  | .bool => 1
  | .fn _ _ _ => 2
  | .hand _ _ _ _ => 3

/-- Pin: computation types are pairs of a value type and an effect set. -/
theorem cty_pin (A : VTy Op) (Δ : Finset Op) :
    (CTy.mk A Δ).res = A ∧ (CTy.mk A Δ).eff = Δ ∧ ∀ C : CTy Op, C = ⟨C.res, C.eff⟩ :=
  ⟨rfl, rfl, fun _ => rfl⟩

/-- Pin: the values and their constructors. -/
example : (ℕ → Val Op) × Val Op × Val Op × Val Op × (Comp Op → Val Op) ×
    (Comp Op → List (Op × Comp Op) → Val Op) :=
  (.var, .unit, .tt, .ff, .lam, .hdl)

/-- Pin: the computations and their constructors. -/
example : (Val Op → Comp Op) × (Op → Val Op → Comp Op) × (Comp Op → Comp Op → Comp Op) ×
    (Val Op → Comp Op → Comp Op → Comp Op) × (Val Op → Val Op → Comp Op) ×
    (Val Op → Comp Op → Comp Op) :=
  (.ret, .op, .bind, .ite, .app, .handle)

/-- Pin: `Val` has exactly these constructors. -/
def valTag : Val Op → ℕ
  | .var _ => 0
  | .unit => 1
  | .tt => 2
  | .ff => 3
  | .lam _ => 4
  | .hdl _ _ => 5

/-- Pin: `Comp` has exactly these constructors. -/
def compTag : Comp Op → ℕ
  | .ret _ => 0
  | .op _ _ => 1
  | .bind _ _ => 2
  | .ite _ _ _ => 3
  | .app _ _ => 4
  | .handle _ _ => 5

/-- Pin: the evaluation contexts and their constructors; a handler frame holds a handler literal,
given by its return clause and its operation clauses. -/
example : ECtx Op × (ECtx Op → Comp Op → ECtx Op) ×
    (Comp Op → List (Op × Comp Op) → ECtx Op → ECtx Op) :=
  (.hole, .bindF, .handleF)

/-- Pin: `ECtx` has exactly these constructors. -/
def ectxTag : ECtx Op → ℕ
  | .hole => 0
  | .bindF _ _ => 1
  | .handleF _ _ _ => 2

end SyntaxPins

/-! ### Pins: operations -/

section OperationPins

variable {Op : Type u}

/-- Pin: renaming values, computations and clauses; under a binder the renaming is lifted by
`References.Term.liftRen`. -/
theorem ren_pin (ρ : ℕ → ℕ) (i : ℕ) (o : Op) (v w : Val Op) (c c₁ c₂ : Comp Op)
    (cls : List (Op × Comp Op)) :
    (Val.var i : Val Op).ren ρ = .var (ρ i) ∧ (Val.unit : Val Op).ren ρ = .unit ∧
    (Val.tt : Val Op).ren ρ = .tt ∧ (Val.ff : Val Op).ren ρ = .ff ∧
    (Val.lam c).ren ρ = .lam (c.ren (References.Term.liftRen ρ)) ∧
    (Val.hdl c cls).ren ρ = .hdl (c.ren (References.Term.liftRen ρ)) (Clauses.ren ρ cls) ∧
    (Comp.ret v).ren ρ = .ret (v.ren ρ) ∧ (Comp.op o v).ren ρ = .op o (v.ren ρ) ∧
    (Comp.bind c₁ c₂).ren ρ = .bind (c₁.ren ρ) (c₂.ren (References.Term.liftRen ρ)) ∧
    (Comp.ite v c₁ c₂).ren ρ = .ite (v.ren ρ) (c₁.ren ρ) (c₂.ren ρ) ∧
    (Comp.app v w).ren ρ = .app (v.ren ρ) (w.ren ρ) ∧
    (Comp.handle v c).ren ρ = .handle (v.ren ρ) (c.ren ρ) ∧
    Clauses.ren ρ ([] : List (Op × Comp Op)) = [] ∧
    Clauses.ren ρ ((o, c) :: cls) =
      (o, c.ren (References.Term.liftRen (References.Term.liftRen ρ))) :: Clauses.ren ρ cls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Val.ren, Comp.ren, Clauses.ren]

/-- Pin: lifting a substitution. -/
theorem liftSub_pin (σ : ℕ → Val Op) (i : ℕ) :
    liftSub σ 0 = .var 0 ∧ liftSub σ (i + 1) = (σ i).ren (· + 1) :=
  ⟨rfl, rfl⟩

/-- Pin: substituting into values, computations and clauses. -/
theorem subst_pin (σ : ℕ → Val Op) (i : ℕ) (o : Op) (v w : Val Op) (c c₁ c₂ : Comp Op)
    (cls : List (Op × Comp Op)) :
    (Val.var i).subst σ = σ i ∧ (Val.unit : Val Op).subst σ = .unit ∧
    (Val.tt : Val Op).subst σ = .tt ∧ (Val.ff : Val Op).subst σ = .ff ∧
    (Val.lam c).subst σ = .lam (c.subst (liftSub σ)) ∧
    (Val.hdl c cls).subst σ = .hdl (c.subst (liftSub σ)) (Clauses.subst σ cls) ∧
    (Comp.ret v).subst σ = .ret (v.subst σ) ∧ (Comp.op o v).subst σ = .op o (v.subst σ) ∧
    (Comp.bind c₁ c₂).subst σ = .bind (c₁.subst σ) (c₂.subst (liftSub σ)) ∧
    (Comp.ite v c₁ c₂).subst σ = .ite (v.subst σ) (c₁.subst σ) (c₂.subst σ) ∧
    (Comp.app v w).subst σ = .app (v.subst σ) (w.subst σ) ∧
    (Comp.handle v c).subst σ = .handle (v.subst σ) (c.subst σ) ∧
    Clauses.subst σ ([] : List (Op × Comp Op)) = [] ∧
    Clauses.subst σ ((o, c) :: cls) =
      (o, c.subst (liftSub (liftSub σ))) :: Clauses.subst σ cls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Val.subst, Comp.subst, Clauses.subst]

/-- Pin: the single and double instantiation substitutions. -/
theorem instSub_pin (v x k : Val Op) (i : ℕ) :
    singleSub v 0 = v ∧ singleSub v (i + 1) = .var i ∧
    doubleSub x k 0 = k ∧ doubleSub x k 1 = x ∧ doubleSub x k (i + 2) = .var i :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Pin: instantiation is substitution by `singleSub` and `doubleSub`. -/
theorem inst_pin (w v x k : Val Op) (c : Comp Op) :
    w.inst v = w.subst (singleSub v) ∧ c.inst v = c.subst (singleSub v) ∧
    c.inst₂ x k = c.subst (doubleSub x k) :=
  ⟨rfl, rfl, rfl⟩

/-- Pin: plugging a context; a handler frame plugs as the handler literal `.hdl cr cls`. -/
theorem plug_pin (E : ECtx Op) (c c₂ cr : Comp Op) (cls : List (Op × Comp Op)) :
    ECtx.hole.plug c = c ∧ (ECtx.bindF E c₂).plug c = .bind (E.plug c) c₂ ∧
    (ECtx.handleF cr cls E).plug c = .handle (.hdl cr cls) (E.plug c) :=
  ⟨rfl, rfl, rfl⟩

/-- Pin: renaming a context lifts the renaming over the computation of a `do` frame and renames
the handler literal of a handler frame as `Val.ren` does. -/
theorem ectx_ren_pin (ρ : ℕ → ℕ) (E : ECtx Op) (c c₂ cr : Comp Op)
    (cls : List (Op × Comp Op)) :
    ECtx.hole.ren ρ = (.hole : ECtx Op) ∧
    (ECtx.bindF E c₂).ren ρ = .bindF (E.ren ρ) (c₂.ren (References.Term.liftRen ρ)) ∧
    (ECtx.handleF cr cls E).ren ρ =
      .handleF (cr.ren (References.Term.liftRen ρ)) (Clauses.ren ρ cls) (E.ren ρ) ∧
    ((ECtx.handleF cr cls E).ren ρ).plug c = .handle ((Val.hdl cr cls).ren ρ) ((E.ren ρ).plug c) :=
  ⟨rfl, rfl, rfl, rfl⟩

variable [DecidableEq Op]

/-- Pin: clauses are looked up with `List.lookup`, which takes the first clause for an
operation. -/
theorem lookup_first_match_pin (o : Op) (c₁ c₂ : Comp Op) (cls : List (Op × Comp Op)) :
    ((o, c₁) :: (o, c₂) :: cls).lookup o = some c₁ := by
  simp [List.lookup]

/-- Pin: the operations handled by a value. -/
theorem ops_pin (c : Comp Op) (cls : List (Op × Comp Op)) (i : ℕ) :
    (Val.hdl c cls).ops = (cls.map Prod.fst).toFinset ∧ (Val.var i : Val Op).ops = ∅ ∧
    (Val.unit : Val Op).ops = ∅ ∧ (Val.tt : Val Op).ops = ∅ ∧ (Val.ff : Val Op).ops = ∅ ∧
    (Val.lam c).ops = ∅ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Pin: the operations handled by a context. -/
theorem handled_pin (E : ECtx Op) (c₂ cr : Comp Op) (cls : List (Op × Comp Op)) :
    ECtx.hole.handled = (∅ : Finset Op) ∧ (ECtx.bindF E c₂).handled = E.handled ∧
    (ECtx.handleF cr cls E).handled = (Val.hdl cr cls).ops ∪ E.handled :=
  ⟨rfl, rfl, rfl⟩

/-- Pin: answers. -/
theorem answer_pin (c : Comp Op) :
    c.Answer ↔ (∃ v, c = .ret v) ∨
      ∃ (E : ECtx Op) (o : Op) (v : Val Op), c = E.plug (.op o v) ∧ o ∉ E.handled :=
  Iff.rfl

end OperationPins

/-! ### Pins: typing rules -/

section TypingPins

variable {Op : Type u} [DecidableEq Op] {sig : Op → VTy Op × VTy Op} {Γ : List (VTy Op)}

theorem HasVTy.var_pin {i : ℕ} {A : VTy Op} (h : Γ[i]? = some A) :
    HasVTy sig Γ (.var i) A :=
  .var h

theorem HasVTy.consts_pin :
    HasVTy sig Γ .unit .unit ∧ HasVTy sig Γ .tt .bool ∧ HasVTy sig Γ .ff .bool :=
  ⟨.unit, .tt, .ff⟩

theorem HasVTy.lam_pin {A B : VTy Op} {Δ : Finset Op} {c : Comp Op}
    (h : HasCTy sig (A :: Γ) c ⟨B, Δ⟩) : HasVTy sig Γ (.lam c) (.fn A B Δ) :=
  .lam h

theorem HasVTy.hdl_pin {A B : VTy Op} {Δ Δ' : Finset Op} {cr : Comp Op}
    {cls : List (Op × Comp Op)} (hr : HasCTy sig (A :: Γ) cr ⟨B, Δ'⟩)
    (hcls : HasClauses sig Γ cls B Δ') (hΔ : Δ \ (Val.hdl cr cls).ops ⊆ Δ') :
    HasVTy sig Γ (.hdl cr cls) (.hand A Δ B Δ') :=
  .hdl hr hcls hΔ

theorem HasCTy.ret_pin {v : Val Op} {A : VTy Op} {Δ : Finset Op} (h : HasVTy sig Γ v A) :
    HasCTy sig Γ (.ret v) ⟨A, Δ⟩ :=
  .ret h

theorem HasCTy.op_pin {o : Op} {v : Val Op} {Δ : Finset Op} (ho : o ∈ Δ)
    (h : HasVTy sig Γ v (sig o).1) : HasCTy sig Γ (.op o v) ⟨(sig o).2, Δ⟩ :=
  .op ho h

theorem HasCTy.bind_pin {c₁ c₂ : Comp Op} {A B : VTy Op} {Δ : Finset Op}
    (h₁ : HasCTy sig Γ c₁ ⟨A, Δ⟩) (h₂ : HasCTy sig (A :: Γ) c₂ ⟨B, Δ⟩) :
    HasCTy sig Γ (.bind c₁ c₂) ⟨B, Δ⟩ :=
  .bind h₁ h₂

theorem HasCTy.ite_pin {v : Val Op} {c₁ c₂ : Comp Op} {C : CTy Op}
    (hv : HasVTy sig Γ v .bool) (h₁ : HasCTy sig Γ c₁ C) (h₂ : HasCTy sig Γ c₂ C) :
    HasCTy sig Γ (.ite v c₁ c₂) C :=
  .ite hv h₁ h₂

theorem HasCTy.app_pin {v w : Val Op} {A B : VTy Op} {Δ : Finset Op}
    (hv : HasVTy sig Γ v (.fn A B Δ)) (hw : HasVTy sig Γ w A) :
    HasCTy sig Γ (.app v w) ⟨B, Δ⟩ :=
  .app hv hw

theorem HasCTy.handle_pin {h : Val Op} {c : Comp Op} {A B : VTy Op} {Δ Δ' : Finset Op}
    (hh : HasVTy sig Γ h (.hand A Δ B Δ')) (hc : HasCTy sig Γ c ⟨A, Δ⟩) :
    HasCTy sig Γ (.handle h c) ⟨B, Δ'⟩ :=
  .handle hh hc

theorem HasClauses.nil_pin {B : VTy Op} {Δ' : Finset Op} : HasClauses sig Γ [] B Δ' :=
  .nil

theorem HasClauses.cons_pin {o : Op} {c : Comp Op} {cls : List (Op × Comp Op)} {B : VTy Op}
    {Δ' : Finset Op} (hc : HasCTy sig (.fn (sig o).2 B Δ' :: (sig o).1 :: Γ) c ⟨B, Δ'⟩)
    (hcls : HasClauses sig Γ cls B Δ') : HasClauses sig Γ ((o, c) :: cls) B Δ' :=
  .cons hc hcls

end TypingPins

/-! ### Pins: step rules -/

section StepPins

variable {Op : Type u} [DecidableEq Op]

theorem Step.beta_pin (c : Comp Op) (v : Val Op) (c₁ c₂ : Comp Op) :
    Step (.app (.lam c) v) (c.inst v) ∧ Step (.ite .tt c₁ c₂) c₁ ∧ Step (.ite .ff c₁ c₂) c₂ ∧
    Step (.bind (.ret v) c) (c.inst v) :=
  ⟨.appLam, .iteTrue, .iteFalse, .bindRet⟩

theorem Step.handleRet_pin (cr : Comp Op) (cls : List (Op × Comp Op)) (v : Val Op) :
    Step (.handle (.hdl cr cls) (.ret v)) (cr.inst v) :=
  .handleRet

theorem Step.handleOp_pin {cr : Comp Op} {cls : List (Op × Comp Op)} {E : ECtx Op} {o : Op}
    {v : Val Op} {c : Comp Op} (hc : cls.lookup o = some c) (hE : o ∉ E.handled) :
    Step (.handle (.hdl cr cls) (E.plug (.op o v)))
      (c.inst₂ v (.lam (.handle ((Val.hdl cr cls).ren (· + 1))
        ((E.ren (· + 1)).plug (.ret (.var 0)))))) :=
  .handleOp hc hE

theorem Step.cong_pin {c₁ c₁' c₂ cr : Comp Op} {cls : List (Op × Comp Op)} (hs : Step c₁ c₁') :
    Step (.bind c₁ c₂) (.bind c₁' c₂) ∧
      Step (.handle (.hdl cr cls) c₁) (.handle (.hdl cr cls) c₁') :=
  ⟨.bindCong hs, .handleCong hs⟩

end StepPins

/-! ### Local helper facts -/

section Helpers

variable {Op : Type u}

/-- A plugged context is an operation call only when the context is the hole. -/
theorem plug_eq_op {E : ECtx Op} {c : Comp Op} {o : Op} {v : Val Op}
    (h : E.plug c = .op o v) : E = .hole ∧ c = .op o v := by
  cases E with
  | hole => exact ⟨rfl, h⟩
  | bindF E c₂ => simp [ECtx.plug] at h
  | handleF cr cls E => simp [ECtx.plug] at h

/-- An operation call does not step. -/
theorem op_normal [DecidableEq Op] (o : Op) (v : Val Op) : Relation.Normal Step (Comp.op o v) := by
  rintro ⟨c', h⟩
  cases h

end Helpers

/-! ### T1: a state handler -/

/-- The operations of a boolean state. -/
inductive StOp where
  /-- `get : unit → bool`. -/
  | get : StOp
  /-- `set : bool → unit`. -/
  | set : StOp
  deriving DecidableEq

/-- The signature of the state operations. -/
def stSig : StOp → VTy StOp × VTy StOp
  | .get => (.unit, .bool)
  | .set => (.bool, .unit)

/-- The state handler, returning a function of the initial state:
`return x ↦ return (fun s ↦ return x)`, `get(_; k) ↦ return (fun s ↦ do f ← k s in f s)`,
`set(s; k) ↦ return (fun _ ↦ do f ← k () in f s)`. -/
def stH : Val StOp :=
  .hdl (.ret (.lam (.ret (.var 1))))
    [(.get, .ret (.lam (.bind (.app (.var 1) (.var 0)) (.app (.var 0) (.var 1))))),
     (.set, .ret (.lam (.bind (.app (.var 1) .unit) (.app (.var 0) (.var 3)))))]

/-- `do b ← get () in if b then set false else set true`. -/
def flipState : Comp StOp :=
  .bind (.op .get .unit) (.ite (.var 0) (.op .set .ff) (.op .set .tt))

theorem stH_typed :
    HasVTy stSig [] stH (.hand .unit {.get, .set} (.fn .bool .unit ∅) ∅) := by
  refine .hdl (.ret (.lam (.ret (.var rfl)))) (.cons ?_ (.cons ?_ .nil)) (by decide)
  · exact .ret (.lam (.bind (.app (.var rfl) (.var rfl)) (.app (.var rfl) (.var rfl))))
  · exact .ret (.lam (.bind (.app (.var rfl) .unit) (.app (.var rfl) (.var rfl))))

theorem flipState_typed : HasCTy stSig [] flipState ⟨.unit, {.get, .set}⟩ :=
  .bind (.op (by decide) .unit) (.ite (.var rfl) (.op (by decide) .ff) (.op (by decide) .tt))

/-- **T1.** The handled program is a pure computation returning a function of the initial
state. -/
theorem handle_flipState_typed :
    HasCTy stSig [] (.handle stH flipState) ⟨.fn .bool .unit ∅, ∅⟩ :=
  .handle stH_typed flipState_typed

/-! ### T2: operations outside the effect set -/

/-- **T2.** An operation call has no type with an empty effect set. -/
theorem op_not_typed_empty {Op : Type u} [DecidableEq Op] {sig : Op → VTy Op × VTy Op}
    {Γ : List (VTy Op)} {o : Op} {v : Val Op} {B : VTy Op} :
    ¬ HasCTy sig Γ (.op o v) ⟨B, ∅⟩ := by
  intro h
  cases h with
  | op ho _ => simp at ho

/-- With `get` in the effect set the call is typed. -/
theorem get_typed : HasCTy stSig [] (.op .get .unit) ⟨.bool, {.get}⟩ :=
  .op (by decide) .unit

/-! ### T3: unhandled operations must be forwarded -/

/-- A handler for `set` only: `return x ↦ return x`, `set(_; k) ↦ k ()`. -/
def setOnly : Val StOp :=
  .hdl (.ret (.var 0)) [(.set, .app (.var 0) .unit)]

/-- **T3.** A handler that neither handles nor forwards `get` is ill-typed. -/
theorem setOnly_not_typed : ¬ HasVTy stSig [] setOnly (.hand .unit {.get} .unit ∅) := by
  intro h
  cases h with
  | hdl _ _ hΔ => exact absurd hΔ (by decide)

/-- Forwarding `get` makes the same handler typable. -/
theorem setOnly_typed_forwarding : HasVTy stSig [] setOnly (.hand .unit {.get} .unit {.get}) :=
  .hdl (.ret (.var rfl)) (.cons (.app (.var rfl) .unit) .nil) (by decide)

/-! ### T4: result change without answer-type modification -/

/-- `return x ↦ return true`, `get(_; k) ↦ k false`. -/
def toBool : Val StOp :=
  .hdl (.ret .tt) [(.get, .app (.var 0) .ff)]

/-- **T4, positive.** The return clause changes the result type from `unit` to `bool`. -/
theorem toBool_typed : HasVTy stSig [] toBool (.hand .unit {.get} .bool ∅) :=
  .hdl (.ret .tt) (.cons (.app (.var rfl) .ff) .nil) (by decide)

/-- `do f ← k false in f true`: uses the continuation as if it returned a function. -/
def atmClause : Comp StOp :=
  .bind (.app (.var 0) .ff) (.app (.var 0) .tt)

/-- The clause is typable when the continuation returns a function `bool → bool ! ∅`. -/
theorem atmClause_typed_other_answer :
    HasCTy stSig [.fn .bool (.fn .bool .bool ∅) ∅, .unit] atmClause ⟨.bool, ∅⟩ :=
  .bind (.app (.var rfl) .ff) (.app (.var rfl) .tt)

/-- **T4, negative.** In a handler of type `unit ! {get} ⇒ bool ! ∅` the continuation returns
`bool ! ∅`, so a clause that uses it at another answer type is ill-typed. -/
theorem atm_not_typed :
    ¬ HasVTy stSig [] (.hdl (.ret .tt) [(.get, atmClause)]) (.hand .unit {.get} .bool ∅) := by
  intro h
  cases h with
  | hdl _ hcls _ =>
    cases hcls with
    | cons hc _ =>
      cases hc with
      | bind h₁ h₂ =>
        cases h₁ with
        | app hv _ =>
          cases hv with
          | var hk =>
            simp only [stSig] at hk
            obtain ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ := Option.some.inj hk
            cases h₂ with
            | app hf _ =>
              cases hf with
              | var hf => simp at hf

/-! ### T5: deep handling -/

/-- A single operation `tick : unit → unit`. -/
inductive Tick where
  /-- The operation. -/
  | tick : Tick
  deriving DecidableEq

/-- The resuming handler: `return x ↦ return x`, `tick(_; k) ↦ k ()`. -/
def resume : Val Tick :=
  .hdl (.ret (.var 0)) [(.tick, .app (.var 0) .unit)]

/-- `do _ ← tick () in tick ()`. -/
def twice : Comp Tick :=
  .bind (.op .tick .unit) (.op .tick .unit)

/-- **T5.** Both calls are caught: the continuation of the first call re-installs the handler
around the rest of the program. -/
theorem resume_twice : Relation.ReflTransGen Step (.handle resume twice) (.ret .unit) := by
  have s₁ : Step (.handle resume twice)
      (.app (.lam (.handle resume (.bind (.ret (.var 0)) (.op .tick .unit)))) .unit) :=
    Step.handleOp (cr := .ret (.var 0)) (cls := [(Tick.tick, .app (.var 0) .unit)])
      (E := .bindF .hole (.op Tick.tick .unit)) (o := Tick.tick) (v := .unit)
      (c := .app (.var 0) .unit) rfl (by decide)
  have s₂ : Step (.app (.lam (.handle resume (.bind (.ret (.var 0)) (.op .tick .unit)))) .unit)
      (.handle resume (.bind (.ret .unit) (.op .tick .unit))) :=
    Step.appLam
  have s₃ : Step (.handle resume (.bind (.ret .unit) (.op .tick .unit)))
      (.handle resume (.op .tick .unit)) :=
    Step.handleCong Step.bindRet
  have s₄ : Step (.handle resume (.op .tick .unit))
      (.app (.lam (.handle resume (.ret (.var 0)))) .unit) :=
    Step.handleOp (cr := .ret (.var 0)) (cls := [(Tick.tick, .app (.var 0) .unit)])
      (E := .hole) (o := Tick.tick) (v := .unit) (c := .app (.var 0) .unit) rfl (by decide)
  have s₅ : Step (.app (.lam (.handle resume (.ret (.var 0)))) .unit)
      (.handle resume (.ret .unit)) :=
    Step.appLam
  have s₆ : Step (.handle resume (.ret .unit)) (.ret .unit) :=
    Step.handleRet
  exact .head s₁ (.head s₂ (.head s₃ (.head s₄ (.head s₅ (.single s₆)))))

/-! ### T6: handler-delimited contexts -/

/-- Two operations `a, b : unit → unit`. -/
inductive Two where
  /-- The first operation. -/
  | a : Two
  /-- The second operation. -/
  | b : Two
  deriving DecidableEq

/-- An outer handler for both operations, answering `true`. -/
def outer : Val Two :=
  .hdl (.ret (.var 0)) [(.a, .ret .tt), (.b, .ret .tt)]

/-- An inner handler for `a` only, answering `false`. -/
def inner : Val Two :=
  .hdl (.ret (.var 0)) [(.a, .ret .ff)]

/-- The outer handler's rule is blocked for `a`: the frame of the handler literal `inner`
handles it. -/
theorem a_mem_handled :
    Two.a ∈ (ECtx.handleF (.ret (.var 0)) [(Two.a, .ret .ff)] .hole).handled := by
  decide

/-- **T6.** Of two nested handlers for `a`, only the inner one fires. -/
theorem nested_step_iff (c' : Comp Two) :
    Step (.handle outer (.handle inner (.op .a .unit))) c' ↔
      c' = .handle outer (.ret .ff) := by
  constructor
  · intro hs
    generalize ht : Comp.handle outer (.handle inner (.op .a .unit)) = t at hs
    cases hs with
    | appLam => cases ht
    | iteTrue => cases ht
    | iteFalse => cases ht
    | bindRet => cases ht
    | handleRet => cases ht
    | bindCong _ => cases ht
    | @handleOp cr cls E o v c hc hE =>
      injection ht with _ hE'
      cases E with
      | hole => cases hE'
      | bindF E c₂ => cases hE'
      | handleF cr' cls' E =>
        injection hE' with hh hp
        obtain ⟨rfl, hop⟩ := plug_eq_op hp.symm
        injection hop with ho _
        subst ho
        cases hh
        exact absurd a_mem_handled hE
    | @handleCong cr cls c c'' hc =>
      injection ht with hh hc'
      subst hc'
      rw [← hh]
      generalize ht' : Comp.handle inner (.op .a .unit) = t' at hc
      cases hc with
      | appLam => cases ht'
      | iteTrue => cases ht'
      | iteFalse => cases ht'
      | bindRet => cases ht'
      | handleRet => injection ht' with _ h'; cases h'
      | bindCong _ => cases ht'
      | @handleOp cr₁ cls₁ E o v c hc hE =>
        injection ht' with hh₁ hp
        obtain ⟨rfl, hop⟩ := plug_eq_op hp.symm
        injection hop with ho hv
        subst ho hv
        cases hh₁
        simp [List.lookup] at hc
        subst hc
        rfl
      | handleCong hs => injection ht' with _ h'; subst h'; exact absurd ⟨_, hs⟩ (op_normal _ _)
  · rintro rfl
    exact .handleCong (.handleOp (E := .hole) (c := .ret .ff) rfl (by decide))

/-- **T6.** An operation the inner handler does not handle is caught by the outer handler in
one step. -/
theorem outer_catches_b :
    Step (.handle outer (.handle inner (.op .b .unit))) (.ret .tt) :=
  .handleOp (E := .handleF (.ret (.var 0)) [(Two.a, .ret .ff)] .hole) (c := .ret .tt) rfl
    (by decide)

/-- **T6.** There is no forwarding step: the inner handler alone leaves the call to `b` as it
is. -/
theorem inner_b_normal : Relation.Normal Step (.handle inner (.op .b .unit)) := by
  rintro ⟨c', hs⟩
  generalize ht : Comp.handle inner (.op .b .unit) = t at hs
  cases hs with
  | appLam => cases ht
  | iteTrue => cases ht
  | iteFalse => cases ht
  | bindRet => cases ht
  | handleRet => injection ht with _ h'; cases h'
  | bindCong _ => cases ht
  | @handleOp cr cls E o v c hc hE =>
    injection ht with hh hp
    obtain ⟨rfl, hop⟩ := plug_eq_op hp.symm
    injection hop with ho _
    subst ho
    cases hh
    simp [List.lookup, show (Two.b == Two.a) = false from rfl] at hc
  | handleCong hs => injection ht with _ h'; subst h'; exact op_normal _ _ ⟨_, hs⟩

/-- **T6, variable handler.** In `with outer handle (with x handle a ())`, where the inner
handler is the variable `x`, nothing steps: a variable forms no handler frame, so the outer
handler does not catch the call to `a`, and no step is taken under the variable. -/
theorem var_handler_normal :
    Relation.Normal Step (.handle outer (.handle (.var 0) (.op Two.a .unit))) := by
  rintro ⟨c', hs⟩
  generalize ht : Comp.handle outer (.handle (.var 0) (.op Two.a .unit)) = t at hs
  cases hs with
  | appLam => cases ht
  | iteTrue => cases ht
  | iteFalse => cases ht
  | bindRet => cases ht
  | handleRet => cases ht
  | bindCong _ => cases ht
  | @handleOp cr cls E o v c hc hE =>
    injection ht with _ hE'
    cases E with
    | hole => cases hE'
    | bindF E c₂ => cases hE'
    | handleF cr' cls' E => cases hE'
  | @handleCong cr cls c c'' hc =>
    injection ht with _ hc'
    subst hc'
    generalize ht' : Comp.handle (.var 0) (.op Two.a .unit) = t' at hc
    cases hc <;> cases ht'

/-- **T6, variable handler, after substitution.** Substituting the handler literal `inner` for
the variable gives the nested literal handlers of `nested_step_iff`, where the inner handler
catches `a`. Before the substitution no handler caught the call (`var_handler_normal`), so the
substitution does not change which handler catches it. -/
theorem var_handler_inst_step_iff (c' : Comp Two) :
    Step ((Comp.handle outer (.handle (.var 0) (.op Two.a .unit))).inst inner) c' ↔
      c' = .handle outer (.ret .ff) := by
  have h : (Comp.handle outer (.handle (.var 0) (.op Two.a .unit))).inst inner =
      .handle outer (.handle inner (.op .a .unit)) := rfl
  rw [h]
  exact nested_step_iff c'

/-- **T6, variable handler, congruence.** No step is taken under a handler given by a variable,
while the same computation steps under the handler literal `inner`. -/
theorem var_handler_no_cong :
    Relation.Normal Step (Comp.handle (.var 0) (.bind (.ret .unit) (.op Two.a .unit))) ∧
      Step (Comp.handle inner (.bind (.ret .unit) (.op Two.a .unit)))
        (.handle inner (.op .a .unit)) := by
  refine ⟨?_, .handleCong .bindRet⟩
  rintro ⟨c', hs⟩
  generalize ht : Comp.handle (.var 0) (.bind (.ret .unit) (.op Two.a .unit)) = t at hs
  cases hs <;> cases ht

/-! ### T7: answers -/

section Answers

variable {Op : Type u} [DecidableEq Op]

/-- **T7.** A returned value is an answer and a normal form. -/
theorem ret_answer_normal (v : Val Op) :
    (Comp.ret v).Answer ∧ Relation.Normal Step (Comp.ret v) := by
  refine ⟨.inl ⟨v, rfl⟩, ?_⟩
  rintro ⟨c', h⟩
  cases h

/-- **T7.** An operation call is an answer and a normal form. -/
theorem op_answer_normal (o : Op) (v : Val Op) :
    (Comp.op o v).Answer ∧ Relation.Normal Step (Comp.op o v) :=
  ⟨.inr ⟨.hole, o, v, rfl, by simp [ECtx.handled]⟩, op_normal o v⟩

/-- **T7.** An operation call under a `do` frame is an answer and a normal form. -/
theorem bind_op_answer_normal (o : Op) (v : Val Op) (c : Comp Op) :
    (Comp.bind (.op o v) c).Answer ∧ Relation.Normal Step (Comp.bind (.op o v) c) := by
  refine ⟨.inr ⟨.bindF .hole c, o, v, rfl, by simp [ECtx.handled]⟩, ?_⟩
  rintro ⟨c', h⟩
  cases h with
  | bindCong h => exact op_normal o v ⟨_, h⟩

end Answers

/-- **T7.** A call caught by an enclosing handler is not an answer. -/
theorem caught_not_answer : ¬ (Comp.handle inner (.op .a .unit)).Answer := by
  rintro (⟨v, h⟩ | ⟨E, o, v, h, hE⟩)
  · cases h
  · cases E with
    | hole => cases h
    | bindF E c₂ => cases h
    | handleF cr cls E =>
      injection h with hh hp
      obtain ⟨rfl, hop⟩ := plug_eq_op hp.symm
      injection hop with ho _
      subst ho
      cases hh
      exact hE (by decide)

/-- **T7, handler literal.** A call that the handler literal `inner` does not handle is an
answer, with `inner` as a handler frame. -/
theorem literal_uncaught_answer : (Comp.handle inner (.op .b .unit)).Answer :=
  .inr ⟨.handleF (.ret (.var 0)) [(Two.a, .ret .ff)] .hole, .b, .unit, rfl, by decide⟩

/-- **T7, variable handler.** The call in `with outer handle (with x handle a ())`, where the
inner handler is the variable `x`, is not an answer. -/
theorem var_handler_not_answer :
    ¬ (Comp.handle outer (.handle (.var 0) (.op Two.a .unit))).Answer := by
  rintro (⟨v, h⟩ | ⟨E, o, v, h, hE⟩)
  · cases h
  · cases E with
    | hole => cases h
    | bindF E c₂ => cases h
    | handleF cr cls E =>
      injection h with _ hp
      cases E with
      | hole => cases hp
      | bindF E c₂ => cases hp
      | handleF cr' cls' E => cases hp

/-- **T7, non-handler values.** For every operation `o` and value `v`, a call to `o` under a
variable or under `()` in handler position is not an answer: neither value forms a handler
frame. -/
theorem nonhandler_not_answer {Op : Type u} [DecidableEq Op] (o : Op) (v : Val Op) :
    ¬ (Comp.handle (.var 0) (.op o v)).Answer ∧ ¬ (Comp.handle .unit (.op o v)).Answer := by
  constructor <;>
  · rintro (⟨w, h⟩ | ⟨E, o', w, h, hE⟩)
    · cases h
    · cases E with
      | hole => cases h
      | bindF E c₂ => cases h
      | handleF cr cls E => cases h

/-! ### T8: Pretnar's operation rule is derivable -/

/-- **T8.** `do y ← op o v in c` has type `A ! Δ` exactly when `o ∈ Δ`, `v : A_o`, and `c` has
type `A ! Δ` under `y : B_o`: Pretnar's rule for `op(v; y. c)` (2015, Fig. 6). -/
theorem bind_op_typed_iff {Op : Type u} [DecidableEq Op] {sig : Op → VTy Op × VTy Op}
    {Γ : List (VTy Op)} {o : Op} {v : Val Op} {c : Comp Op} {A : VTy Op} {Δ : Finset Op} :
    HasCTy sig Γ (.bind (.op o v) c) ⟨A, Δ⟩ ↔
      o ∈ Δ ∧ HasVTy sig Γ v (sig o).1 ∧ HasCTy sig ((sig o).2 :: Γ) c ⟨A, Δ⟩ := by
  constructor
  · intro h
    cases h with
    | bind h₁ h₂ =>
      cases h₁ with
      | op ho hv => exact ⟨ho, hv, h₂⟩
  · rintro ⟨ho, hv, hc⟩
    exact .bind (.op ho hv) hc

end BasicTests

end Cslib.Languages.LambdaCalculus.EffectHandlers
