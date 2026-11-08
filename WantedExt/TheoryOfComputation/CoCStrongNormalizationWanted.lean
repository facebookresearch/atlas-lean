/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strong normalization and consistency for the calculus of constructions with a universe hierarchy

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ProgramVerification.CoCStrongNormalization` — coc_strong_normalization (manifest `manifests/problems/coc_strong_normalization.toml`, rev 1, submitter Kim Morrison, status draft) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted` namespace. Mathematical
statements are unchanged. Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010).
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.Init

@[expose] public section

namespace MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
namespace ProgramVerification
namespace CoCStrongNormalization

/-- Sorts: an impredicative `Prop` and a predicative hierarchy `Type 0`, `Type 1`, ... -/
inductive Srt where
  | prop : Srt
  | type : Nat → Srt
  deriving DecidableEq, Repr, Inhabited

/-- Terms, with de Bruijn variables. -/
inductive Tm where
  | var : Nat → Tm
  | srt : Srt → Tm
  | app : Tm → Tm → Tm
  /-- `lam A b` is `λ (x : A). b`. -/
  | lam : Tm → Tm → Tm
  /-- `pi A B` is `Π (x : A). B`. -/
  | pi : Tm → Tm → Tm
  deriving DecidableEq, Repr, Inhabited

/-- `lift d c t` adds `d` to every free variable of `t` at index `c` or above. -/
def lift (d c : Nat) : Tm → Tm
  | .var i => if i < c then .var i else .var (i + d)
  | .srt s => .srt s
  | .app f a => .app (lift d c f) (lift d c a)
  | .lam A b => .lam (lift d c A) (lift d (c + 1) b)
  | .pi A B => .pi (lift d c A) (lift d (c + 1) B)

/-- `subst k u t` replaces variable `k` of `t` by `u`, decrementing the variables above `k`. -/
def subst (k : Nat) (u : Tm) : Tm → Tm
  | .var i => if i < k then .var i else if i = k then lift k 0 u else .var (i - 1)
  | .srt s => .srt s
  | .app f a => .app (subst k u f) (subst k u a)
  | .lam A b => .lam (subst k u A) (subst (k + 1) u b)
  | .pi A B => .pi (subst k u A) (subst (k + 1) u B)

/-- One step of beta reduction, under any context. -/
inductive Step : Tm → Tm → Prop where
  | beta (A b a : Tm) : Step (.app (.lam A b) a) (subst 0 a b)
  | appFun {f f' : Tm} (a : Tm) : Step f f' → Step (.app f a) (.app f' a)
  | appArg (f : Tm) {a a' : Tm} : Step a a' → Step (.app f a) (.app f a')
  | lamTy {A A' : Tm} (b : Tm) : Step A A' → Step (.lam A b) (.lam A' b)
  | lamBody (A : Tm) {b b' : Tm} : Step b b' → Step (.lam A b) (.lam A b')
  | piDom {A A' : Tm} (B : Tm) : Step A A' → Step (.pi A B) (.pi A' B)
  | piCod (A : Tm) {B B' : Tm} : Step B B' → Step (.pi A B) (.pi A B')

/-- Beta conversion: the equivalence closure of `Step`. -/
inductive Conv : Tm → Tm → Prop where
  | refl (t : Tm) : Conv t t
  | fwd {t u v : Tm} : Conv t u → Step u v → Conv t v
  | bwd {t u v : Tm} : Conv t u → Step v u → Conv t v

/-- `Ax s s'` says that the sort `s` is itself typed by the sort `s'`. -/
inductive Ax : Srt → Srt → Prop where
  | prop : Ax .prop (.type 0)
  | type (i : Nat) : Ax (.type i) (.type (i + 1))

/--
`Rl s₁ s₂ s₃` says a `Π` whose domain lives in `s₁` and whose codomain lives in `s₂` itself
lives in `s₃`. The first constructor is the impredicativity of `Prop`.
-/
inductive Rl : Srt → Srt → Srt → Prop where
  | prop (s : Srt) : Rl s .prop .prop
  | type (i j : Nat) : Rl (.type i) (.type j) (.type (max i j))
  | propType (i : Nat) : Rl .prop (.type i) (.type i)

mutual

/-- Well-formedness of a context; the head of the list is the most recent binding. -/
inductive Wf : List Tm → Prop where
  | nil : Wf []
  | cons {Γ : List Tm} {A : Tm} {s : Srt} : Wf Γ → Typing Γ A (.srt s) → Wf (A :: Γ)

/-- The typing judgement. -/
inductive Typing : List Tm → Tm → Tm → Prop where
  | srt {Γ : List Tm} {s s' : Srt} : Wf Γ → Ax s s' → Typing Γ (.srt s) (.srt s')
  | var {Γ : List Tm} {i : Nat} {A : Tm} :
      Wf Γ → Γ[i]? = some A → Typing Γ (.var i) (lift (i + 1) 0 A)
  | pi {Γ : List Tm} {A B : Tm} {s₁ s₂ s₃ : Srt} :
      Typing Γ A (.srt s₁) → Typing (A :: Γ) B (.srt s₂) → Rl s₁ s₂ s₃ →
      Typing Γ (.pi A B) (.srt s₃)
  | lam {Γ : List Tm} {A B b : Tm} {s : Srt} :
      Typing Γ (.pi A B) (.srt s) → Typing (A :: Γ) b B →
      Typing Γ (.lam A b) (.pi A B)
  | app {Γ : List Tm} {f a A B : Tm} :
      Typing Γ f (.pi A B) → Typing Γ a A →
      Typing Γ (.app f a) (subst 0 a B)
  | conv {Γ : List Tm} {t A B : Tm} {s : Srt} :
      Typing Γ t A → Typing Γ B (.srt s) → Conv A B → Typing Γ t B

end

/-- `t` is strongly normalizing: there is no infinite chain of `Step`s out of `t`. -/
def SN (t : Tm) : Prop := Acc (fun u v => Step v u) t

end CoCStrongNormalization
end ProgramVerification

/-!
# Strong normalization for the calculus of constructions with universes

## The system

`Tm` is the usual lambda syntax with de Bruijn variables: variables, sorts, application,
`lam A b` for `λ (x : A). b`, and `pi A B` for `Π (x : A). B`. The sorts `Srt` are an
impredicative `Prop` together with a predicative hierarchy `Type 0`, `Type 1`, ..., typed by
`Ax`, which gives `Prop : Type 0` and `Type i : Type (i+1)`. This is the non-cumulative,
Π-only generalized calculus of constructions CCω: its concrete sort-formation and product
rules agree with Lean's `Prop`/`Type i` hierarchy, while omitting Lean's inductive types,
proof irrelevance, and other extensions. Products are formed by `Rl`, where
`Rl s₁ s₂ s₃` says a `Π` with domain in `s₁` and codomain in `s₂` lands in `s₃`; the three
rules are the impredicative `Rl s .prop .prop`, the predicative
`Rl (.type i) (.type j) (.type (max i j))`, and `Rl .prop (.type i) (.type i)`. There is no
cumulativity. `Step` is beta reduction under any context, `Conv` its equivalence closure, and
`Wf`/`Typing` the mutually defined context-well-formedness and typing judgements. Finally,
`SN t` says `t` admits no infinite chain of `Step`s, expressed as accessibility for the
reversed relation.

Reading the syntax takes a moment, so as a worked example, `λ (A : Prop). λ (x : A). x` is

    Tm.lam (.srt .prop) (.lam (.var 0) (.var 0))

and its type `Π (A : Prop). Π (x : A). A` is

    Tm.pi (.srt .prop) (.pi (.var 0) (.var 1))

where `A` is `.var 0` under one binder and `.var 1` under two.

## The task

Prove six things about this system.

* `typing_polyId`: the term above really does have the type above. This one is short.
* `typing_polyId_app`: applying it to `False` is well typed, exercising `Typing.app`.
* `step_polyId_app`: that application takes the expected beta step, exercising `subst`.
* `subject_reduction`: if `Γ ⊢ t : A` and `t` steps to `t'`, then `Γ ⊢ t' : A`.
* `strong_normalization`: every well-typed term is strongly normalizing.
* `consistency`: no closed term has type `Π (P : Prop). P`, which in this syntax is
  `Tm.pi (.srt .prop) (.var 0)`.

`strong_normalization` is the substantial one. The obstacle is the impredicative rule
`Rl s .prop .prop`: a proposition may quantify over domains in `Prop` or any `Type i`, so no
induction on the structure of types can get off the ground, and one needs Girard's reducibility
candidates adapted to dependent types. Coquand and Huet introduced the calculus of
constructions; Luo proved strong normalization for the stronger extended calculus with a
predicative universe hierarchy, and Barras formalized sound models of CC and CCω. Given
normalization, subject reduction, confluence, and the corresponding canonical-form analysis,
`consistency` follows by analysing closed normal forms: an inhabitant of
`Π (P : Prop). P` would have to be a `lam` whose body is a normal term of type `P` in the
context `[Prop]`, and the only variable available there has type `Prop`, not `P`.

For a smaller rehearsal, replace the hierarchy by the two sorts `Prop` and `Type 0`, and drop
the axiom `Type 0 : Type 1` so that `Type 0` is a top sort. The four surviving product rules
give the usual λC presentation. This is a different typing relation, rather than literally a
subsystem obtained by restricting the terms of CCω, but it keeps the impredicativity while
dropping the hierarchy.

## Design notes

No mathlib is needed and nothing here is executable, so there is no definition hole to game;
the holes are all theorems about a fixed trusted system.

The three small guards exercise the statement itself. If the typing rules were mis-stated so
that nothing were typable, both `strong_normalization` and `consistency` would hold vacuously.
Requiring the polymorphic identity to be typable rules that out, and it exercises
impredicativity on the way, since `Π (A : Prop). A → A` lands in `Prop` only because
`Rl (.type 0) .prop .prop` is available. The application and step guards additionally pin down
`Typing.app`, beta reduction, and substitution.
-/

namespace ProgramVerification
namespace CoCStrongNormalization

/-! ## The problem -/

/--
Anti-vacuity guard: the polymorphic identity `λ (A : Prop). λ (x : A). x` has type
`Π (A : Prop). Π (x : A). A`. This is typable only because `Prop` is impredicative.
Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted typing_polyId :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1)))

/--
Anti-vacuity guard: applying the polymorphic identity to `False` exercises application typing.
Here `False` is encoded as `Π (P : Prop). P`.
Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted typing_polyId_app :
    Typing []
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.pi (.pi (.srt .prop) (.var 0)) (.pi (.srt .prop) (.var 0)))

/- Anti-vacuity guard: the same application takes its expected beta step. -/
/-- Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`. -/
public theorem_wanted step_polyId_app :
    Step
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.lam (.pi (.srt .prop) (.var 0)) (.var 0))

/- Types are preserved by reduction. -/
/-- Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`. -/
public theorem_wanted subject_reduction (Γ : List Tm) (t t' A : Tm) :
    Typing Γ t A → Step t t' → Typing Γ t' A

/- Every well-typed term is strongly normalizing. -/
/-- Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`. -/
public theorem_wanted strong_normalization (Γ : List Tm) (t A : Tm) :
    Typing Γ t A → SN t

/- The system is logically consistent: `Π (P : Prop). P` is not inhabited. -/
/-- Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via leanprover/lean-eval@38361be, problem `coc_strong_normalization`. -/
public theorem_wanted consistency : ¬ ∃ t : Tm, Typing [] t (.pi (.srt .prop) (.var 0))

end CoCStrongNormalization
end ProgramVerification

end MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
