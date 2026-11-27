/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.Exceptions.Safety

/-!
# Tests for the calculus with exceptions

Tests E-T1 to E-T10: `raise` has every type; propagation through a non-handler frame and then
the handler; an uncaught exception is final, a normal form and not a value; a handled value and
nested handlers, where the inner handler catches first and its re-raise reaches the outer one;
negative typing checks (the raised value must have the exception type, the handler must have
the type of the body, a stuck term is ill-typed); progress fails without the uncaught-exception
clause; the schema instances on a concrete term, and syntactic soundness with the answers of a
handled and an unhandled program typed at the type of the program; and `raise` at exception type
`bot` as ex falso. Tests that go through a statement of `Exceptions.Safety` are proved by
applying that statement; every other fact is proved directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.Exceptions

namespace SafetyTests

/-! ### Local helper facts -/

/-- **A term that steps is not a value.** No left-hand side of a step is an abstraction or a
numeral. -/
theorem not_value_of_step {e e' : Term} (h : Step e e') : ¬ e.Value := by
  intro hv
  cases h with
  | beta => cases hv
  | mul => cases hv
  | ifzZero => cases hv
  | ifzSucc => cases hv
  | @propagate F v _ _ _ => cases F <;> cases hv
  | tryValue => cases hv
  | tryRaise => cases hv
  | @frame F _ _ _ _ => cases F <;> cases hv

/-- **An uncaught exception of a numeral does not step.** For every `n`, `raise n` is a normal
form. -/
theorem raise_num_normal (n : ℕ) : Relation.Normal Step (.raise (.num n)) := by
  rintro ⟨e', h⟩
  generalize ht : Term.raise (.num n) = t at h
  cases h with
  | beta => cases ht
  | mul => cases ht
  | ifzZero => cases ht
  | ifzSucc => cases ht
  | @propagate F v _ _ _ => cases F <;> simp [Frame.plug] at ht
  | tryValue => cases ht
  | tryRaise => cases ht
  | @frame F e₁ e₂ _ hs =>
    cases F <;> simp [Frame.plug] at ht
    subst ht
    exact not_value_of_step hs (.num n)

/-! ### E-T1: raise has every type -/

/-- **E-T1: raise has every type.** At exception type `nat`, `raise 3` has every type `A`. -/
theorem raise_has_every_type (A : Ty) : HasType .nat [] (.raise (.num 3)) A :=
  .raise .num

/-! ### E-T2: propagation, then the handler -/

/-- **The program of E-T2.** The term `try (2 * raise 3) with x. x`. -/
def tryMulRaise : Term :=
  .tryWith (.mul (.num 2) (.raise (.num 3))) (.var 0)

/-- **E-T2: propagation through a non-handler frame, then the handler.** The raised `3` leaves
the multiplication frame and is caught: `try (2 * raise 3) with x. x` reduces to `3`. -/
theorem tryMulRaise_steps : Relation.ReflTransGen Step tryMulRaise (.num 3) := by
  have s₁ : Step tryMulRaise (.tryWith (.raise (.num 3)) (.var 0)) :=
    Step.frame (F := .tryWith (.var 0)) trivial
      (Step.propagate (F := .mulR (.num 2)) (.num 3) (.num 2) (fun _ h => nomatch h))
  have s₂ : Step (.tryWith (.raise (.num 3)) (.var 0)) (.num 3) :=
    Step.tryRaise (.num 3)
  exact .head s₁ (.single s₂)

/-! ### E-T3: an uncaught exception is final -/

/-- **E-T3: an uncaught exception is a final answer.** `2 * raise 3` reduces to `raise 3`, which
is final and a normal form but not a value. -/
theorem uncaught_final :
    Relation.ReflTransGen Step (.mul (.num 2) (.raise (.num 3))) (.raise (.num 3)) ∧
      Final (.raise (.num 3)) ∧ Relation.Normal Step (.raise (.num 3)) ∧
      ¬ (Term.raise (.num 3)).Value :=
  ⟨.single (Step.propagate (F := .mulR (.num 2)) (.num 3) (.num 2) (fun _ h => nomatch h)),
    .inr ⟨.num 3, .num 3, rfl⟩, raise_num_normal 3, fun h => nomatch h⟩

/-! ### E-T4: a handled value and nested handlers -/

/-- **E-T4: a handled value.** `try 5 with x. 0` steps to `5`. -/
theorem try_value_step : Step (.tryWith (.num 5) (.num 0)) (.num 5) :=
  Step.tryValue (.num 5)

/-- **The program of E-T4.** The term `try (try raise 1 with x. raise (x * 7)) with y. y`. -/
def nestedTry : Term :=
  .tryWith (.tryWith (.raise (.num 1)) (.raise (.mul (.var 0) (.num 7)))) (.var 0)

/-- **E-T4: nested handlers.** The inner handler catches `raise 1` first; its re-raise of `7`
reaches the outer handler: `try (try raise 1 with x. raise (x * 7)) with y. y` reduces to
`7`. -/
theorem nestedTry_steps : Relation.ReflTransGen Step nestedTry (.num 7) := by
  have s₁ : Step nestedTry (.tryWith (.raise (.mul (.num 1) (.num 7))) (.var 0)) :=
    Step.frame (F := .tryWith (.var 0)) trivial (Step.tryRaise (.num 1))
  have s₂ : Step (.tryWith (.raise (.mul (.num 1) (.num 7))) (.var 0))
      (.tryWith (.raise (.num 7)) (.var 0)) :=
    Step.frame (F := .tryWith (.var 0)) trivial
      (Step.frame (F := .raise) trivial (Step.mul (m := 1) (n := 7)))
  have s₃ : Step (.tryWith (.raise (.num 7)) (.var 0)) (.num 7) :=
    Step.tryRaise (.num 7)
  exact .head s₁ (.head s₂ (.single s₃))

/-! ### E-T5 to E-T7: negative typing checks -/

/-- **E-T5: the raised value must have the exception type.** At exception type `nat`,
`raise (λx. x)` has no type. -/
theorem raise_lam_not_typed (A : Ty) : ¬ HasType .nat [] (.raise (.lam (.var 0))) A := by
  intro h
  cases h with
  | raise h => cases h

/-- **E-T6: the handler must have the type of the body.** At exception type `nat`,
`try 1 with x. λy. y` has no type `nat`. -/
theorem handler_type_mismatch : ¬ HasType .nat [] (.tryWith (.num 1) (.lam (.var 0))) .nat := by
  intro h
  cases h with
  | tryWith _ h₂ => cases h₂

/-- **E-T7: a stuck term is ill-typed.** For every exception type `exn`, `1 2` has no type,
while it is a normal form that is not final. -/
theorem stuck_not_typed (exn A : Ty) :
    ¬ HasType exn [] (.app (.num 1) (.num 2)) A ∧ ¬ Final (.app (.num 1) (.num 2)) ∧
      Relation.Normal Step (.app (.num 1) (.num 2)) := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · cases h with
    | app hf _ => cases hf
  · rintro (h | ⟨v, _, h⟩)
    · cases h
    · cases h
  · rintro ⟨e', h⟩
    generalize ht : Term.app (.num 1) (.num 2) = t at h
    cases h with
    | beta => cases ht
    | mul => cases ht
    | ifzZero => cases ht
    | ifzSucc => cases ht
    | @propagate F v _ _ _ => cases F <;> simp [Frame.plug] at ht
    | tryValue => cases ht
    | tryRaise => cases ht
    | @frame F e₁ e₂ _ hs =>
      cases F <;> simp [Frame.plug] at ht
      · obtain ⟨rfl, -⟩ := ht
        exact not_value_of_step hs (.num 1)
      · obtain ⟨-, rfl⟩ := ht
        exact not_value_of_step hs (.num 2)

/-! ### E-T8: progress needs the uncaught-exception clause -/

/-- **E-T8: progress fails without the uncaught-exception clause.** It is not the case that
every closed well-typed term at exception type `nat` is a value or steps: `raise 0` is
neither. -/
theorem progress_needs_uncaught :
    ¬ ∀ (e : Term) (A : Ty), HasType .nat [] e A → e.Value ∨ ∃ e', Step e e' := by
  intro h
  rcases h (.raise (.num 0)) .nat (.raise .num) with hv | hs
  · cases hv
  · exact raise_num_normal 0 hs

/-! ### E-T9: the schema instances on a concrete term -/

/-- **The program of E-T2 is typed.** At exception type `nat`, `try (2 * raise 3) with x. x`
has type `nat`. -/
theorem tryMulRaise_typed : HasType .nat [] tryMulRaise .nat :=
  .tryWith (.mul .num (.raise .num)) (.var rfl)

/-- **E-T9: multi-step safety on a concrete term.** Every term reachable from
`try (2 * raise 3) with x. x` is final or steps, and none is stuck; in particular its result
`3` is final. -/
theorem tryMulRaise_safe {e' : Term} (hr : Relation.ReflTransGen Step tryMulRaise e') :
    (Final e' ∨ ∃ e'', Step e' e'') ∧ ¬ (¬ Final e' ∧ Relation.Normal Step e') :=
  ⟨final_or_step tryMulRaise_typed hr, not_stuck tryMulRaise_typed hr⟩

/-- **E-T9: the result through the schema.** The result `3` of the program of E-T2 is final or
steps. -/
theorem tryMulRaise_result_final : Final (.num 3) ∨ ∃ e'', Step (.num 3) e'' :=
  final_or_step tryMulRaise_typed tryMulRaise_steps

/-- **E-T9: the statement of syntactic soundness.** For every exception type `exn`, every term
reachable from a closed term of type `A` has type `A` and is final or takes a step. -/
theorem hasType_and_final_or_step_pin :
    ∀ {exn : Ty} {e e' : Term} {A : Ty}, HasType exn [] e A → Relation.ReflTransGen Step e e' →
      HasType exn [] e' A ∧ (Final e' ∨ ∃ e'', Step e' e'') :=
  @hasType_and_final_or_step

/-- **E-T9: typed answers through syntactic soundness.** At exception type `nat`, the handled
program `try (2 * raise 3) with x. x` reaches `3`, and the unhandled program `2 * raise 3`
reaches the uncaught exception `raise 3`; both answers have the type `nat` of their program. -/
theorem typed_answers :
    HasType .nat [] (.num 3) .nat ∧ HasType .nat [] (.raise (.num 3)) .nat :=
  ⟨(hasType_and_final_or_step tryMulRaise_typed tryMulRaise_steps).1,
    (hasType_and_final_or_step (A := .nat) (.mul .num (.raise .num)) uncaught_final.1).1⟩

/-- **E-T9: the structural-typing instance.** Substituting `3` for the handler variable of
`x : nat ⊢ x * x : nat` through the interface gives `3 * 3 : nat`, and weakening by one
variable raises the free variable. -/
theorem structural_examples :
    HasType .nat [] ((Term.mul (.var 0) (.var 0)).instantiate (.num 3)) .nat ∧
      HasType .nat [.bot, .nat] ((Term.var 0).rename (· + 1)) .nat :=
  ⟨(structuralTyping .nat).subst (Γ := []) (x := ()) (.mul (.var rfl) (.var rfl)) .num,
    (structuralTyping .nat).weaken (Γ := [.nat]) (Δ := [.bot, .nat]) ⟨[.bot], rfl⟩
      (.var rfl)⟩

/-! ### E-T10: raise at exception type bot -/

/-- **E-T10: raise at exception type `bot` is ex falso.** At exception type `bot`, a variable
of type `bot` raised has every type. -/
theorem raise_bot_efq (A : Ty) : HasType .bot [.bot] (.raise (.var 0)) A :=
  .raise (.var rfl)

end SafetyTests

end Cslib.Languages.LambdaCalculus.Exceptions
