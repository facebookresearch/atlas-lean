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

public import CSLibExt.Languages.LambdaCalculus.CoC.Reduction

/-!
# Typing for the calculus of constructions

This module extracts beta conversion, the sort and product rules, and the mutual context and
term typing judgements unchanged from `WantedExt.TheoryOfComputation.CoCStrongNormalizationWanted`.
It retains their historical namespace and proves the original `typing_polyId` statement.
-/

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
public theorem typing_polyId :
    Typing [] (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
      (.pi (.srt .prop) (.pi (.var 0) (.var 1))) := by
  have hProp : Typing [] (.srt .prop) (.srt (.type 0)) := .srt .nil .prop
  have hΓ : Wf [.srt .prop] := .cons .nil hProp
  have hA : Typing [.srt .prop] (.var 0) (.srt .prop) :=
    Typing.var (A := .srt .prop) hΓ rfl
  have hΓA : Wf [.var 0, .srt .prop] := .cons hΓ hA
  have hA' : Typing [.var 0, .srt .prop] (.var 1) (.srt .prop) :=
    Typing.var (A := .srt .prop) hΓA rfl
  have hx : Typing [.var 0, .srt .prop] (.var 0) (.var 1) :=
    Typing.var (A := .var 0) hΓA rfl
  have hPi : Typing [.srt .prop] (.pi (.var 0) (.var 1)) (.srt .prop) :=
    .pi hA hA' (.prop .prop)
  exact .lam (.pi hProp hPi (.prop (.type 0))) (.lam hPi hx)

end CoCStrongNormalization
end ProgramVerification
end MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
