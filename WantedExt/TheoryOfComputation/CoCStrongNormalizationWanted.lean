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
public import CSLibExt.Languages.LambdaCalculus.CoC.Typing

@[expose] public section

namespace MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
namespace ProgramVerification
namespace CoCStrongNormalization

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
