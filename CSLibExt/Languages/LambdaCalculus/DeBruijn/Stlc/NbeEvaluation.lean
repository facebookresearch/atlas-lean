/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Evaluation for normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Nbe

/-!
# Evaluation for normalization by evaluation

This module interprets intrinsically typed terms in the Kripke semantic domain
from `Nbe` and reifies the result.  Correctness with respect to the semantic
equational theory is proved separately in `NbeCorrectness`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ Δ Θ : List (Ty Base)}

/-- **Evaluation into the Kripke semantic domain.** Let $t$ be a term of type $T$ in context
$\Gamma$ and let $\eta$ be a semantic environment interpreting every variable of $\Gamma$ as a
semantic value in context $\Delta$. The evaluation $\operatorname{ev}(t, \eta)$ is the semantic
value of type $T$ in context $\Delta$ defined by recursion on $t$: a variable $x$ evaluates to
$\eta(x)$; an application $f\,a$ evaluates to the semantic function $\operatorname{ev}(f, \eta)$
applied, along the identity renaming of $\Delta$, to $\operatorname{ev}(a, \eta)$; and an
abstraction $\lambda b$ of type $A \to B$, whose body $b$ lies in the context $\Gamma$ extended
by $A$, evaluates to the semantic function that sends a renaming $\rho$ from $\Delta$ to a context
$\Theta$ and a semantic value $a$ of type $A$ in $\Theta$ to $\operatorname{ev}(b, \eta')$, where
$\eta'$ sends the new variable to $a$ and each variable $x$ of $\Gamma$ to $\eta(x)$ renamed along
$\rho$. -/
def nbeEval : {Γ Δ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → SemEnv Δ Γ → Sem Δ A
  | _, _, _, .var x, η => η x
  | _, _, _, .app f a, η => nbeEval f η Var.id (nbeEval a η)
  | _, _, _, .lam body, η => fun ρ a =>
      nbeEval body (SemEnv.cons a (SemEnv.rename ρ η))

@[simp] theorem nbeEval_var (x : Var Γ A) (η : SemEnv Δ Γ) :
    nbeEval (.var x) η = η x := rfl

@[simp] theorem nbeEval_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) (η : SemEnv Δ Γ) :
    nbeEval (.app f a) η = nbeEval f η Var.id (nbeEval a η) := rfl

@[simp] theorem nbeEval_lam_apply (body : Tm (A :: Γ) B) (η : SemEnv Δ Γ)
    (ρ : Ren Δ Θ) (a : Sem Θ A) :
    nbeEval (.lam body) η ρ a =
      nbeEval body (SemEnv.cons a (SemEnv.rename ρ η)) := rfl

/-- **Normalization by evaluation.** For a term $t$ of type $A$ in context $\Gamma$, its normal
form is the beta-normal, eta-long term of type $A$ in context $\Gamma$ obtained by reifying, at
type $A$, the evaluation of $t$ in the identity semantic environment of $\Gamma$, which interprets
each variable as the reflection of that variable. -/
def normalizeNf (t : Tm Γ A) : Nf Γ A := quote A (nbeEval t SemEnv.identity)

/-- **Normalization of terms.** For a term $t$ of type $A$ in context $\Gamma$, its normalized term
is the term of type $A$ in context $\Gamma$ underlying the beta-normal, eta-long normal form of $t$
computed by normalization by evaluation. -/
def normalizeTm (t : Tm Γ A) : Tm Γ A := (normalizeNf t).toTm

@[simp] theorem normalizeTm_eq (t : Tm Γ A) :
    normalizeTm t = (normalizeNf t).toTm := rfl

end Cslib.Languages.LambdaCalculus.Stlc
