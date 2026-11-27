/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.Callcc.Safety

/-!
# Tests for the calculus with callcc and abort

Tests K-T1 to K-T9: `callcc` has the type of Peirce's law, and a variant with the result type
swapped does not; `abort` steps at top level and is never a value; the early-exit product of
Wright and Felleisen's Figure 6 on a list containing `0` reaches `0` by a trace with no
multiplication step, with the product of a list without `0` as positive control; invoking a
continuation discards the pending context; `abort` is typed at the answer type, and the
unrestricted typing of `abort` is not preserved by a step; Griffin's `𝒞` is derivable at
answer type `bot`; a stuck term is ill-typed; and the schema instances on a concrete program,
with syntactic soundness for the abort-free early-exit product typed at answer type `bot`: its
result has the type `nat` of the program, and its first reduct has no type `nat` at answer type
`bot`.
The list of the early-exit product is a list of numbers in Lean, rendered as the recursion of
Figure 6 unrolled into the program; there are no lists in the calculus. Tests that go through a
statement of `Callcc.Safety` are proved by applying that statement; every other fact is proved
directly.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.Callcc

namespace SafetyTests

/-! ### K-T1 and K-T2: Peirce's law -/

/-- **K-T1: callcc has the type of Peirce's law.** At answer type `nat`, `λf. callcc f` has
type `((nat → bot) → nat) → nat`. -/
theorem peirce_nat :
    HasType .nat [] (.lam (.callcc (.var 0))) (.arr (.arr (.arr .nat .bot) .nat) .nat) :=
  peirce

/-- **K-T2: a wrong variant of Peirce's law fails.** For every answer type `T`, `λf. callcc f`
has no type `((nat → (nat → nat)) → (nat → nat)) → nat`, where the result type is swapped. -/
theorem peirce_swapped_not_typed (T : Ty) :
    ¬ HasType T [] (.lam (.callcc (.var 0)))
      (.arr (.arr (.arr .nat (.arr .nat .nat)) (.arr .nat .nat)) .nat) := by
  intro h
  cases h with
  | lam h =>
    cases h with
    | callcc h =>
      cases h with
      | var hx => simp at hx

/-! ### K-T3: abort at top level -/

/-- **K-T3: abort at top level.** `abort 3` steps to `3`, and no `abort e` is a value. -/
theorem abort_top : Step (.abort (.num 3)) (.num 3) ∧ ∀ e : Term, ¬ (Term.abort e).Value :=
  ⟨Step.abort (E := []) trivial, fun _ h => nomatch h⟩

/-! ### K-T4: the early-exit product -/

/-- **The recursion of the early-exit product, unrolled.** The recursion `p` of Wright and
Felleisen's Figure 6 on a list of numbers, with the continuation as variable `0`: the empty
list gives `1`, and `x :: xs` gives `ifz x (k 0) (x * p xs)`. -/
def unroll : List ℕ → Term
  | [] => .num 1
  | x :: xs => .ifz (.num x) (.app (.var 0) (.num 0)) (.mul (.num x) (unroll xs))

/-- **The early-exit product of a list.** The program `callcc (λk. p l)`. -/
def product (xs : List ℕ) : Term :=
  .callcc (.lam (unroll xs))

/-- **The top-level continuation.** The continuation of the empty context, `λx. abort x`. -/
def topK : Term :=
  .lam (.abort (.var 0))

/-- **The continuation of the empty context.** It is `λx. abort x`. -/
theorem reify_nil : ECtx.reify [] = topK :=
  rfl

/-- **The unrolled recursion after the first β-step.** The unrolled recursion with the top-level
continuation substituted for `k`. -/
def unrolled (xs : List ℕ) : Term :=
  (unroll xs).instantiate topK

/-- **One unrolling.** After substitution, `p (x :: xs)` is `ifz x (k 0) (x * p xs)` with the
top-level continuation for `k`. -/
theorem unrolled_cons (x : ℕ) (xs : List ℕ) :
    unrolled (x :: xs) = .ifz (.num x) (.app topK (.num 0)) (.mul (.num x) (unrolled xs)) :=
  rfl

/-- **Program steps that are not multiplications.** Local reductions other than multiplication,
`callcc` and `abort`, each in an admissible context. -/
inductive NoMulStep : Term → Term → Prop
  /-- β-reduction. -/
  | beta {E : ECtx} {b v : Term} (hE : E.Ok) (hv : v.Value) :
      NoMulStep (E.plug (.app (.lam b) v)) (E.plug (b.instantiate v))
  /-- The zero test at zero. -/
  | ifzZero {E : ECtx} {t e : Term} (hE : E.Ok) :
      NoMulStep (E.plug (.ifz (.num 0) t e)) (E.plug t)
  /-- The zero test at a successor. -/
  | ifzSucc {E : ECtx} {n : ℕ} {t e : Term} (hE : E.Ok) :
      NoMulStep (E.plug (.ifz (.num (n + 1)) t e)) (E.plug e)
  /-- `callcc`. -/
  | callcc {E : ECtx} {v : Term} (hE : E.Ok) (hv : v.Value) :
      NoMulStep (E.plug (.callcc v)) (E.plug (.app v E.reify))
  /-- `abort`. -/
  | abort {E : ECtx} {e : Term} (hE : E.Ok) : NoMulStep (E.plug (.abort e)) e

/-- **Steps without multiplication are steps.** Every `NoMulStep` is a `Step`. -/
theorem NoMulStep.step {e e' : Term} (h : NoMulStep e e') : Step e e' := by
  cases h with
  | beta hE hv => exact .red hE (.beta hv)
  | ifzZero hE => exact .red hE .ifzZero
  | ifzSucc hE => exact .red hE .ifzSucc
  | callcc hE hv => exact .callcc hE hv
  | abort hE => exact .abort hE

/-- **K-T4: the early-exit product.** The product of `[2, 3, 0, 5]` reaches `0` by a trace of
seven steps none of which is a multiplication: on meeting `0` the program invokes the
continuation of the whole computation, which discards the pending multiplications by `3` and
`2`. -/
theorem product_early_exit : Relation.ReflTransGen NoMulStep (product [2, 3, 0, 5]) (.num 0) := by
  have s₁ : NoMulStep (product [2, 3, 0, 5]) (.app (.lam (unroll [2, 3, 0, 5])) topK) :=
    NoMulStep.callcc (E := []) trivial (.lam _)
  have s₂ : NoMulStep (.app (.lam (unroll [2, 3, 0, 5])) topK) (unrolled [2, 3, 0, 5]) :=
    NoMulStep.beta (E := []) trivial (.lam _)
  have s₃ : NoMulStep (unrolled [2, 3, 0, 5]) (.mul (.num 2) (unrolled [3, 0, 5])) :=
    NoMulStep.ifzSucc (E := []) (n := 1) trivial
  have s₄ : NoMulStep (.mul (.num 2) (unrolled [3, 0, 5]))
      (.mul (.num 2) (.mul (.num 3) (unrolled [0, 5]))) :=
    NoMulStep.ifzSucc (E := [.mulR (.num 2)]) (n := 2) ⟨.num 2, trivial⟩
  have s₅ : NoMulStep (.mul (.num 2) (.mul (.num 3) (unrolled [0, 5])))
      (.mul (.num 2) (.mul (.num 3) (.app topK (.num 0)))) :=
    NoMulStep.ifzZero (E := [.mulR (.num 3), .mulR (.num 2)]) ⟨.num 3, .num 2, trivial⟩
  have s₆ : NoMulStep (.mul (.num 2) (.mul (.num 3) (.app topK (.num 0))))
      (.mul (.num 2) (.mul (.num 3) (.abort (.num 0)))) :=
    NoMulStep.beta (E := [.mulR (.num 3), .mulR (.num 2)]) ⟨.num 3, .num 2, trivial⟩ (.num 0)
  have s₇ : NoMulStep (.mul (.num 2) (.mul (.num 3) (.abort (.num 0)))) (.num 0) :=
    NoMulStep.abort (E := [.mulR (.num 3), .mulR (.num 2)]) ⟨.num 3, .num 2, trivial⟩
  exact .head s₁ (.head s₂ (.head s₃ (.head s₄ (.head s₅ (.head s₆ (.single s₇))))))

/-- **K-T4: the early-exit product in the step relation.** -/
theorem product_early_exit_steps : Relation.ReflTransGen Step (product [2, 3, 0, 5]) (.num 0) :=
  Relation.ReflTransGen.mono (fun _ _ h => NoMulStep.step h) _ _ product_early_exit

/-- **K-T4, positive control.** The product of `[2, 3, 5]`, which has no `0`, reduces to `30`,
through three multiplications. -/
theorem product_no_zero : Relation.ReflTransGen Step (product [2, 3, 5]) (.num 30) := by
  have s₁ : Step (product [2, 3, 5]) (.app (.lam (unroll [2, 3, 5])) topK) :=
    Step.callcc (E := []) trivial (.lam _)
  have s₂ : Step (.app (.lam (unroll [2, 3, 5])) topK) (unrolled [2, 3, 5]) :=
    Step.red (E := []) trivial (.beta (.lam _))
  have s₃ : Step (unrolled [2, 3, 5]) (.mul (.num 2) (unrolled [3, 5])) :=
    Step.red (E := []) trivial (.ifzSucc (n := 1))
  have s₄ : Step (.mul (.num 2) (unrolled [3, 5])) (.mul (.num 2) (.mul (.num 3) (unrolled [5]))) :=
    Step.red (E := [.mulR (.num 2)]) ⟨.num 2, trivial⟩ (.ifzSucc (n := 2))
  have s₅ : Step (.mul (.num 2) (.mul (.num 3) (unrolled [5])))
      (.mul (.num 2) (.mul (.num 3) (.mul (.num 5) (.num 1)))) :=
    Step.red (E := [.mulR (.num 3), .mulR (.num 2)]) ⟨.num 3, .num 2, trivial⟩
      (.ifzSucc (n := 4))
  have s₆ : Step (.mul (.num 2) (.mul (.num 3) (.mul (.num 5) (.num 1))))
      (.mul (.num 2) (.mul (.num 3) (.num 5))) :=
    Step.red (E := [.mulR (.num 3), .mulR (.num 2)]) ⟨.num 3, .num 2, trivial⟩
      (.mul (m := 5) (n := 1))
  have s₇ : Step (.mul (.num 2) (.mul (.num 3) (.num 5))) (.mul (.num 2) (.num 15)) :=
    Step.red (E := [.mulR (.num 2)]) ⟨.num 2, trivial⟩ (.mul (m := 3) (n := 5))
  have s₈ : Step (.mul (.num 2) (.num 15)) (.num 30) :=
    Step.red (E := []) trivial (.mul (m := 2) (n := 15))
  exact .head s₁ (.head s₂ (.head s₃ (.head s₄ (.head s₅ (.head s₆ (.head s₇ (.single s₈)))))))

/-! ### K-T5: invoking a continuation discards the pending context -/

/-- **The program of K-T5.** The term `2 * callcc (λk. 10 * k 3)`. -/
def jump : Term :=
  .mul (.num 2) (.callcc (.lam (.mul (.num 10) (.app (.var 0) (.num 3)))))

/-- **K-T5: invoking the continuation discards the pending context.** `2 * callcc (λk. 10 * k 3)`
reduces to `6`: calling `k` with `3` returns `3` to the context `2 * □` and drops `10 * □`. -/
theorem jump_steps : Relation.ReflTransGen Step jump (.num 6) := by
  have s₁ : Step jump (.mul (.num 2) (.app (.lam (.mul (.num 10) (.app (.var 0) (.num 3))))
      (.lam (.abort (.mul (.num 2) (.var 0)))))) :=
    Step.callcc (E := [.mulR (.num 2)]) ⟨.num 2, trivial⟩ (.lam _)
  have s₂ : Step (.mul (.num 2) (.app (.lam (.mul (.num 10) (.app (.var 0) (.num 3))))
      (.lam (.abort (.mul (.num 2) (.var 0))))))
      (.mul (.num 2) (.mul (.num 10) (.app (.lam (.abort (.mul (.num 2) (.var 0)))) (.num 3)))) :=
    Step.red (E := [.mulR (.num 2)]) ⟨.num 2, trivial⟩ (.beta (.lam _))
  have s₃ : Step
      (.mul (.num 2) (.mul (.num 10) (.app (.lam (.abort (.mul (.num 2) (.var 0)))) (.num 3))))
      (.mul (.num 2) (.mul (.num 10) (.abort (.mul (.num 2) (.num 3))))) :=
    Step.red (E := [.mulR (.num 10), .mulR (.num 2)]) ⟨.num 10, .num 2, trivial⟩ (.beta (.num 3))
  have s₄ : Step (.mul (.num 2) (.mul (.num 10) (.abort (.mul (.num 2) (.num 3)))))
      (.mul (.num 2) (.num 3)) :=
    Step.abort (E := [.mulR (.num 10), .mulR (.num 2)]) ⟨.num 10, .num 2, trivial⟩
  have s₅ : Step (.mul (.num 2) (.num 3)) (.num 6) :=
    Step.red (E := []) trivial (.mul (m := 2) (n := 3))
  exact .head s₁ (.head s₂ (.head s₃ (.head s₄ (.single s₅))))

/-! ### K-T6: abort is typed at the answer type -/

/-- **K-T6: the argument of abort must have the answer type.** At answer type `nat`,
`abort (λx. x)` has no type. -/
theorem abort_lam_not_typed (B : Ty) : ¬ HasType .nat [] (.abort (.lam (.var 0))) B := by
  intro h
  cases h with
  | abort h => cases h

/-- **Typing with unrestricted abort.** Wright and Felleisen's unrestricted rule for `abort`:
`abort e` has every type when `e` has some type. -/
inductive NaiveHasType : List Ty → Term → Ty → Prop
  /-- Variables. -/
  | var {Γ : List Ty} {i : ℕ} {A : Ty} (h : Γ[i]? = some A) : NaiveHasType Γ (.var i) A
  /-- Abstraction. -/
  | lam {Γ : List Ty} {A B : Ty} {b : Term} (h : NaiveHasType (A :: Γ) b B) :
      NaiveHasType Γ (.lam b) (.arr A B)
  /-- Application. -/
  | app {Γ : List Ty} {A B : Ty} {f a : Term} (hf : NaiveHasType Γ f (.arr A B))
      (ha : NaiveHasType Γ a A) : NaiveHasType Γ (.app f a) B
  /-- Numerals. -/
  | num {Γ : List Ty} {n : ℕ} : NaiveHasType Γ (.num n) .nat
  /-- Multiplication. -/
  | mul {Γ : List Ty} {a b : Term} (ha : NaiveHasType Γ a .nat) (hb : NaiveHasType Γ b .nat) :
      NaiveHasType Γ (.mul a b) .nat
  /-- The zero test. -/
  | ifz {Γ : List Ty} {A : Ty} {c t e : Term} (hc : NaiveHasType Γ c .nat)
      (ht : NaiveHasType Γ t A) (he : NaiveHasType Γ e A) : NaiveHasType Γ (.ifz c t e) A
  /-- `callcc`. -/
  | callcc {Γ : List Ty} {A B : Ty} {e : Term} (h : NaiveHasType Γ e (.arr (.arr A B) A)) :
      NaiveHasType Γ (.callcc e) A
  /-- Unrestricted `abort`. -/
  | abort {Γ : List Ty} {A B : Ty} {e : Term} (h : NaiveHasType Γ e A) :
      NaiveHasType Γ (.abort e) B

/-- **K-T6: the unrestricted typing of abort is not preserved.** Under the unrestricted rule,
`1 * abort (λx. x)` has type `nat` and steps to `λx. x`, which has no type `nat` (Wright and
Felleisen, §6.3). With abort typed at the answer type `nat` the program is rejected. -/
theorem naive_abort_not_preserved :
    NaiveHasType [] (.mul (.num 1) (.abort (.lam (.var 0)))) .nat ∧
      Step (.mul (.num 1) (.abort (.lam (.var 0)))) (.lam (.var 0)) ∧
      ¬ NaiveHasType [] (.lam (.var 0)) .nat ∧
      ¬ HasType .nat [] (.mul (.num 1) (.abort (.lam (.var 0)))) .nat := by
  refine ⟨.mul .num (.abort (A := .arr .nat .nat) (.lam (.var rfl))),
    Step.abort (E := [.mulR (.num 1)]) ⟨.num 1, trivial⟩, (fun h => nomatch h), fun h => ?_⟩
  cases h with
  | mul _ hb =>
    cases hb with
    | abort h => cases h

/-! ### K-T7: Griffin's 𝒞 at answer type bot -/

/-- **Negation.** The type `X → bot`. -/
abbrev neg (X : Ty) : Ty :=
  .arr X .bot

/-- **K-T7: Griffin's `𝒞` is derivable at answer type `bot`.** For every type `A`, at answer type
`bot`, `λm. callcc (λk. abort (m k))` has type `¬¬A → A`, where `¬X` is `X → bot`. -/
theorem griffin_C (A : Ty) :
    HasType .bot [] (.lam (.callcc (.lam (.abort (.app (.var 1) (.var 0))))))
      (.arr (neg (neg A)) A) :=
  .lam (.callcc (B := .bot) (.lam (.abort (.app (.var rfl) (.var rfl)))))

/-! ### K-T8: stuck terms are ill-typed -/

/-- **K-T8: a stuck term is ill-typed.** For every answer type `T` and type `A`, `1 2` has no
type `A`. -/
theorem stuck_not_typed (T A : Ty) : ¬ HasType T [] (.app (.num 1) (.num 2)) A := by
  intro h
  cases h with
  | app hf _ => cases hf

/-! ### K-T9: the schema instances on a concrete program -/

/-- **The unrolled recursion is typed.** For every answer type `T` and list `xs`, the unrolled
recursion has type `nat` with the continuation of type `nat → nat`. -/
theorem unroll_typed (T : Ty) (xs : List ℕ) : HasType T [.arr .nat .nat] (unroll xs) .nat := by
  induction xs with
  | nil => exact .num
  | cons x xs ih => exact .ifz .num (.app (.var rfl) .num) (.mul .num ih)

/-- **The early-exit product is a program of answer type `nat`.** For every list `xs`, the
product program has type `nat` at answer type `nat`. -/
theorem product_typed (xs : List ℕ) : HasType .nat [] (product xs) .nat :=
  .callcc (B := .nat) (.lam (unroll_typed .nat xs))

/-- **K-T9: multi-step safety on a concrete program.** Every term reachable from the early-exit
product of `[2, 3, 0, 5]`, a closed program of the answer type `nat`, is a value or steps, and
none is stuck; in particular its result `0` is a value or steps. -/
theorem product_safe {e' : Term} (hr : Relation.ReflTransGen Step (product [2, 3, 0, 5]) e') :
    (e'.Value ∨ ∃ e'', Step e' e'') ∧ ¬ (¬ e'.Value ∧ Relation.Normal Step e') :=
  ⟨final_or_step (product_typed _) hr, not_stuck (product_typed _) hr⟩

/-- **K-T9: the result through the schema.** The result `0` of the early-exit product is a value
or steps. -/
theorem product_result : (Term.num 0).Value ∨ ∃ e'', Step (.num 0) e'' :=
  final_or_step (product_typed _) product_early_exit_steps

/-- **The early-exit product contains no abort.** For every list `xs`, the product program is
abort-free. -/
theorem product_abortFree (xs : List ℕ) : (product xs).AbortFree := by
  show (unroll xs).AbortFree
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    show True ∧ (True ∧ True) ∧ True ∧ (unroll xs).AbortFree
    exact ⟨trivial, ⟨trivial, trivial⟩, trivial, ih⟩

/-- **K-T9: the statement of syntactic soundness for abort-free programs.** For every answer type
`T`, every term reachable from an abort-free closed term of type `A` has type `A` at answer type
`A`, and is a value or takes a step. -/
theorem hasType_and_final_or_step_abortFree_pin :
    ∀ {T : Ty} {e e' : Term} {A : Ty}, e.AbortFree → HasType T [] e A →
      Relation.ReflTransGen Step e e' → HasType A [] e' A ∧ (e'.Value ∨ ∃ e'', Step e' e'') :=
  @hasType_and_final_or_step_abortFree

/-- **The early-exit product is typed at answer type `bot`.** For every list `xs`, the product
program has type `nat` at answer type `bot`. -/
theorem product_typed_bot (xs : List ℕ) : HasType .bot [] (product xs) .nat :=
  .callcc (B := .nat) (.lam (unroll_typed .bot xs))

/-- **K-T9: the typed answer of an abort-free program.** Typed at answer type `bot`, the
early-exit product of `[2, 3, 0, 5]` contains no `abort`; its result `0` has the type `nat` of
the program, at answer type `nat`. -/
theorem product_typed_answer : HasType .nat [] (.num 0) .nat :=
  (hasType_and_final_or_step_abortFree (product_abortFree [2, 3, 0, 5]) (product_typed_bot _)
    product_early_exit_steps).1

/-- **K-T9: reached terms are typed at the program's type.** Typed at answer type `bot`, the
early-exit product of `[2, 3, 0, 5]` takes a `callcc` step to a term with no type `nat` at
answer type `bot`, since the continuation `λx. abort x` needs `x : bot`; so syntactic soundness
types the reached terms at answer type `nat`, the type of the program, and not at `bot`. -/
theorem product_step_not_typed_bot :
    HasType .bot [] (product [2, 3, 0, 5]) .nat ∧
      Step (product [2, 3, 0, 5]) (.app (.lam (unroll [2, 3, 0, 5])) topK) ∧
      ¬ HasType .bot [] (.app (.lam (unroll [2, 3, 0, 5])) topK) .nat := by
  refine ⟨product_typed_bot _, Step.callcc (E := []) trivial (.lam _), fun h => ?_⟩
  cases h with
  | app hf ha =>
    cases ha with
    | lam hb =>
      cases hb with
      | abort hx =>
        cases hx with
        | var hx =>
          cases hx
          cases hf with
          | lam hu =>
            cases hu with
            | ifz _ ht _ =>
              cases ht with
              | app hk hn =>
                cases hn
                cases hk with
                | var hk => cases hk

/-- **K-T9: the structural-typing instance.** Substituting `2` for the variable of
`x : nat ⊢ x * x : nat` through the interface gives `2 * 2 : nat`, and weakening by one variable
raises the free variable. -/
theorem structural_examples :
    HasType .nat [] ((Term.mul (.var 0) (.var 0)).instantiate (.num 2)) .nat ∧
      HasType .nat [.bot, .nat] ((Term.var 0).rename (· + 1)) .nat :=
  ⟨(structuralTyping .nat).subst (Γ := []) (x := ()) (.mul (.var rfl) (.var rfl)) .num,
    (structuralTyping .nat).weaken (Γ := [.nat]) (Δ := [.bot, .nat]) ⟨[.bot], rfl⟩
      (.var rfl)⟩

end SafetyTests

end Cslib.Languages.LambdaCalculus.Callcc
