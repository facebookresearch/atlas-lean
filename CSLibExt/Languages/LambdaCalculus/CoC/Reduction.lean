/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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
Adapted from `LeanEval/ProgramVerification/CoCSystem.lean` (sorts, terms,
shifting, substitution, and one-step reduction) and
`LeanEval/ProgramVerification/CoCStrongNormalization.lean` (the statement of
`step_polyId_app`), from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e. Problem `coc_strong_normalization`,
statement revision 1, submitter Kim Morrison. lean-eval ships no `NOTICE` file.
ATLAS previously inlined and documented this syntax and moved it into the
namespace below. This file splits out the operational prefix unchanged and
supplies a proof of the original beta-step statement.
-/

module

public import Mathlib.Init

/-!
# Syntax and one-step beta reduction for the calculus of constructions

The syntax uses de Bruijn indices. The historical namespace is retained so
that the wanted typing and normalization results use exactly the same terms
and reduction relation.
-/

@[expose] public section

namespace MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
namespace ProgramVerification
namespace CoCStrongNormalization

/-- **Sorts of CCω.** The sorts are $\mathrm{Prop}$ and $\mathrm{Type}_i$ for every natural number
$i$. In the calculus, $\mathrm{Prop}$ is impredicative and the $\mathrm{Type}_i$ form a
predicative hierarchy. -/
inductive Srt where
  | prop : Srt
  | type : Nat → Srt
  deriving DecidableEq, Repr, Inhabited

/--
**Terms of the calculus of constructions.** A term is a variable $\#i$ with de Bruijn index
$i \in \mathbb{N}$, a sort $s$ (either $\mathrm{Prop}$ or $\mathrm{Type}_i$ for some
$i \in \mathbb{N}$), an application $f\,a$ of a term $f$ to a term $a$, an abstraction
$\lambda (x : A).\, b$ with domain $A$ and body $b$, or a dependent product
$\Pi (x : A).\, B$ with domain $A$ and codomain $B$.

In the body of an abstraction or the codomain of a product, index $0$ refers to the bound
variable and index $i + 1$ to the variable that has index $i$ outside the binder.
-/
inductive Tm where
  | var : Nat → Tm
  | srt : Srt → Tm
  | app : Tm → Tm → Tm
  /-- `lam A b` is `λ (x : A). b`. -/
  | lam : Tm → Tm → Tm
  /-- `pi A B` is `Π (x : A). B`. -/
  | pi : Tm → Tm → Tm
  deriving DecidableEq, Repr, Inhabited

/-- **Shifting de Bruijn indices.** For natural numbers $d$ and $c$, shifting a term $t$ by $d$
above the cutoff $c$ adds $d$ to every variable index $i \ge c$ and leaves every index $i < c$
unchanged. The cutoff goes up by one under each binder, that is, in the body of a $\lambda$ and
in the codomain of a $\Pi$ (not in the type annotation or the domain), and sorts are unchanged.
Thus the free variables of $t$ with index at least $c$ are increased by $d$. -/
def lift (d c : Nat) : Tm → Tm
  | .var i => if i < c then .var i else .var (i + d)
  | .srt s => .srt s
  | .app f a => .app (lift d c f) (lift d c a)
  | .lam A b => .lam (lift d c A) (lift d (c + 1) b)
  | .pi A B => .pi (lift d c A) (lift d (c + 1) B)

/--
**Substitution for a de Bruijn variable.** For $k \in \mathbb{N}$ and terms $u$ and $t$, the
term $t[k := u]$ is defined by recursion on $t$. For a variable, $\#i[k := u]$ is $\#i$ if
$i < k$, is $u$ with every free variable raised by $k$ if $i = k$, and is $\#(i - 1)$ if
$i > k$. A sort is unchanged, $(f\,a)[k := u] = f[k := u]\,a[k := u]$,
$(\lambda (x : A).\, b)[k := u] = \lambda (x : A[k := u]).\, b[k + 1 := u]$, and
$(\Pi (x : A).\, B)[k := u] = \Pi (x : A[k := u]).\, B[k + 1 := u]$.
-/
def subst (k : Nat) (u : Tm) : Tm → Tm
  | .var i => if i < k then .var i else if i = k then lift k 0 u else .var (i - 1)
  | .srt s => .srt s
  | .app f a => .app (subst k u f) (subst k u a)
  | .lam A b => .lam (subst k u A) (subst (k + 1) u b)
  | .pi A B => .pi (subst k u A) (subst (k + 1) u B)

/-- **One-step beta reduction.** One-step beta reduction is the smallest relation on terms that
contains every beta step $(\lambda (x : A).\, b)\, a \to b[a/x]$, where $b[a/x]$ substitutes $a$
for the bound variable $x$ in $b$, and that is closed under every term former: a step inside the
function or the argument of an application, inside the type annotation or the body of a
$\lambda$, or inside the domain or the codomain of a $\Pi$ is a step of the whole term. -/
inductive Step : Tm → Tm → Prop where
  | beta (A b a : Tm) : Step (.app (.lam A b) a) (subst 0 a b)
  | appFun {f f' : Tm} (a : Tm) : Step f f' → Step (.app f a) (.app f' a)
  | appArg (f : Tm) {a a' : Tm} : Step a a' → Step (.app f a) (.app f a')
  | lamTy {A A' : Tm} (b : Tm) : Step A A' → Step (.lam A b) (.lam A' b)
  | lamBody (A : Tm) {b b' : Tm} : Step b b' → Step (.lam A b) (.lam A b')
  | piDom {A A' : Tm} (B : Tm) : Step A A' → Step (.pi A B) (.pi A' B)
  | piCod (A : Tm) {B B' : Tm} : Step B B' → Step (.pi A B) (.pi A B')

/--
**Beta step of the applied polymorphic identity.** The polymorphic identity
$\lambda (A : \mathrm{Prop}).\, \lambda (x : A).\, x$ applied to
$\bot = \Pi (P : \mathrm{Prop}).\, P$ reduces in one beta step to $\lambda (x : \bot).\, x$.

This is an anti-vacuity guard: it pins down beta reduction and substitution.

Source: Coquand and Huet, 'The calculus of constructions' (1988); Zhaohui Luo, 'An Extended
Calculus of Constructions' (1990); Bruno Barras, 'Sets in Coq, Coq in Sets' (2010). Via
leanprover/lean-eval@38361be, problem `coc_strong_normalization`.
-/
public theorem step_polyId_app :
    Step
      (.app
        (.lam (.srt .prop) (.lam (.var 0) (.var 0)))
        (.pi (.srt .prop) (.var 0)))
      (.lam (.pi (.srt .prop) (.var 0)) (.var 0)) :=
  Step.beta (.srt .prop) (.lam (.var 0) (.var 0)) (.pi (.srt .prop) (.var 0))

end CoCStrongNormalization
end ProgramVerification
end MathlibExt.TheoryOfComputation.CoCStrongNormalizationWanted
