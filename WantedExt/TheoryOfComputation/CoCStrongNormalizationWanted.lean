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
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.ProgramVerification.CoCStrongNormalization` — coc_strong_normalization (manifest
`manifests/problems/coc_strong_normalization.toml`, rev 1, submitter Kim Morrison, status draft) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted`
namespace. Mathematical
statements are unchanged. The inlined system came from
`LeanEval.ProgramVerification.CoCSystem` at the same pin. The operational
prefix and the now-proved `step_polyId_app` are re-exported from
`CSLibExt.Languages.LambdaCalculus.CoC.Reduction`.
Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui
Luo, 'An Extended Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets'
(2010).
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.Init
public import CSLibExt.Languages.LambdaCalculus.CoC.Reduction

@[expose] public section

namespace MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
namespace ProgramVerification
namespace CoCStrongNormalization

/-- **Beta conversion.** Beta conversion is the equivalence closure of one-step beta reduction:
every term is convertible to itself, and if $t$ is convertible to $u$ and $u$ reduces to $v$ in
one step, or $v$ reduces to $u$ in one step, then $t$ is convertible to $v$. -/
inductive Conv : Tm → Tm → Prop where
  | refl (t : Tm) : Conv t t
  | fwd {t u v : Tm} : Conv t u → Step u v → Conv t v
  | bwd {t u v : Tm} : Conv t u → Step v u → Conv t v

/-- **Sort axioms of CCω.** The axioms say which sort has which sort as its type: $\mathrm{Prop}$
has type $\mathrm{Type}_0$, and $\mathrm{Type}_i$ has type $\mathrm{Type}_{i+1}$ for every natural
number $i$. No other pair of sorts is related. -/
inductive Ax : Srt → Srt → Prop where
  | prop : Ax .prop (.type 0)
  | type (i : Nat) : Ax (.type i) (.type (i + 1))

/--
**Product rules of CCω.** The product rules say in which sort $s_3$ a dependent product
$\Pi (x : A).\, B$ lives when $A$ lives in the sort $s_1$ and $B$ lives in the sort $s_2$. There
are exactly three rules: for every sort $s$, a product with domain in $s$ and codomain in
$\mathrm{Prop}$ lives in $\mathrm{Prop}$ (the impredicativity of $\mathrm{Prop}$); for all natural
numbers $i$ and $j$, a product with domain in $\mathrm{Type}_i$ and codomain in $\mathrm{Type}_j$
lives in $\mathrm{Type}_{\max(i, j)}$; and for every natural number $i$, a product with domain in
$\mathrm{Prop}$ and codomain in $\mathrm{Type}_i$ lives in $\mathrm{Type}_i$.
-/
inductive Rl : Srt → Srt → Srt → Prop where
  | prop (s : Srt) : Rl s .prop .prop
  | type (i j : Nat) : Rl (.type i) (.type j) (.type (max i j))
  | propType (i : Nat) : Rl .prop (.type i) (.type i)

mutual

/--
**Well-formed contexts.** A context is a list of terms whose head is the most recent binding.
Well-formedness of contexts is defined together with the typing judgement
$\Gamma \vdash t : A$ as the least predicate such that the empty context is well formed, and
if $\Gamma$ is well formed and $\Gamma \vdash A : s$ for some sort $s$, then the context
obtained from $\Gamma$ by adding $A$ at the head is well formed.
-/
inductive Wf : List Tm → Prop where
  | nil : Wf []
  | cons {Γ : List Tm} {A : Tm} {s : Srt} : Wf Γ → Typing Γ A (.srt s) → Wf (A :: Γ)

/--
**Typing judgement of the calculus of constructions with universes.** A context $\Gamma$ is a
list of terms whose head is the type of the most recent variable; write $\Gamma, A$ for
$\Gamma$ extended by $A$ at the head. The judgement $\Gamma \vdash t : A$ ($t$ has type $A$
in $\Gamma$) is defined together with well-formedness of contexts as the least relation
closed under the following rules.

* Sorts: if $\Gamma$ is well formed and $s : s'$ is an axiom, namely
  $\mathrm{Prop} : \mathrm{Type}_0$ or $\mathrm{Type}_i : \mathrm{Type}_{i+1}$, then
  $\Gamma \vdash s : s'$.
* Variables: if $\Gamma$ is well formed and its entry at position $i$ (counting from $0$ at
  the head) is $A$, then $\Gamma \vdash \#i : A'$, where $A'$ is $A$ with every free variable
  raised by $i + 1$.
* Products: if $\Gamma \vdash A : s_1$, $\Gamma, A \vdash B : s_2$ and $(s_1, s_2, s_3)$ is a
  product rule, namely $(s, \mathrm{Prop}, \mathrm{Prop})$ for a sort $s$,
  $(\mathrm{Type}_i, \mathrm{Type}_j, \mathrm{Type}_{\max(i, j)})$ or
  $(\mathrm{Prop}, \mathrm{Type}_i, \mathrm{Type}_i)$, then
  $\Gamma \vdash \Pi (x : A).\, B : s_3$.
* Abstractions: if $\Gamma \vdash \Pi (x : A).\, B : s$ for some sort $s$ and
  $\Gamma, A \vdash b : B$, then $\Gamma \vdash \lambda (x : A).\, b : \Pi (x : A).\, B$.
* Applications: if $\Gamma \vdash f : \Pi (x : A).\, B$ and $\Gamma \vdash a : A$, then
  $\Gamma \vdash f\,a : B[a]$, where $B[a]$ replaces variable $0$ of $B$ by $a$ and lowers
  the other free variables of $B$ by one.
* Conversion: if $\Gamma \vdash t : A$, $\Gamma \vdash B : s$ for some sort $s$, and $A$ and
  $B$ are beta convertible, then $\Gamma \vdash t : B$.
-/
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

/-- **Strongly normalizing terms.** The strongly normalizing terms are defined inductively: a term
$t$ is strongly normalizing when every term to which $t$ reduces in one beta step is strongly
normalizing. Equivalently, classically, there is no infinite chain of one-step beta reductions
starting from $t$. -/
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
**Typing the polymorphic identity.** In the empty context, the polymorphic identity
$\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ has type
$\Pi (A : \mathrm{Prop}).\, \Pi (x : A).\, A$.

This is typable only because $\mathrm{Prop}$ is impredicative: a product over
$A : \mathrm{Prop}$ whose codomain is a proposition is again a proposition.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus
of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted typing_polyId :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1)))

/--
**Typing the polymorphic identity applied to falsity.** Write $\bot$ for
$\Pi (P : \mathrm{Prop}).\, P$. In the empty context, the application of the polymorphic
identity $\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ to $\bot$ has type
$\Pi (x : \bot).\, \bot$.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended Calculus
of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted typing_polyId_app :
    Typing []
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.pi (.pi (.srt .prop) (.var 0)) (.pi (.srt .prop) (.var 0)))

/- Types are preserved by reduction. -/
/--
**Subject reduction.** Let $\Gamma$ be a context and $t$, $t'$, $A$ terms of the calculus
of constructions with universes. If $t$ has type $A$ in $\Gamma$, that is
$\Gamma \vdash t : A$, and $t$ reduces to $t'$ in one step of beta reduction (anywhere
inside $t$), then $\Gamma \vdash t' : A$.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended
Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted subject_reduction (Γ : List Tm) (t t' A : Tm) :
    Typing Γ t A → Step t t' → Typing Γ t' A

/- Every well-typed term is strongly normalizing. -/
/--
**Strong normalization of CCω.** Every well-typed term is strongly normalizing: if
$\Gamma \vdash t : A$ for some context $\Gamma$ and some term $A$, then $t$ is strongly
normalizing.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended
Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted strong_normalization (Γ : List Tm) (t A : Tm) :
    Typing Γ t A → SN t

/- The system is logically consistent: `Π (P : Prop). P` is not inhabited. -/
/--
**Consistency of CCω.** No closed term has type $\Pi (P : \mathrm{Prop}).\, P$: there is no term
$t$ with $\vdash t : \Pi (P : \mathrm{Prop}).\, P$ in the empty context.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended
Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem_wanted consistency : ¬ ∃ t : Tm, Typing [] t (.pi (.srt .prop) (.var 0))

end CoCStrongNormalization
end ProgramVerification

end MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
