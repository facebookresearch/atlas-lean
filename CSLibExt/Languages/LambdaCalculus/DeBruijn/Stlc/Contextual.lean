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
# Typed term contexts for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Equational

/-!
# Typed term contexts for STLC

This file formalizes one-hole contexts for intrinsically typed STLC terms.
The input and output contexts and types are all tracked by indices, so plugging
is scope-aware and type preserving.  A `lam` context intentionally binds the
leading variable of its hole context.  Contexts compose, plugging respects
composition, and semantic equality is a congruence for every typed context.

The final section packages equality in every same-universe set-theoretic
interpretation as a model-independent equational theory and lifts beta and eta
through contexts.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {A B C D : Ty Base}
variable {Γ Δ Θ Ξ : List (Ty Base)}

/-- **Typed one-hole contexts.** Fix simple types over a type of base types. A one-hole context
whose hole has type $A$ in variable context $\Gamma$, and which produces a term of type $B$ in
variable context $\Delta$, is built by four rules. The hole itself is such a context, with
$\Delta = \Gamma$ and $B = A$. If $C$ produces type $S \Rightarrow T$ in $\Delta$ and $a$ is a term
of type $S$ in $\Delta$, then the application $C\,a$ produces type $T$ in $\Delta$. If $f$ is a
term of type $S \Rightarrow T$ in $\Delta$ and $C$ produces type $S$ in $\Delta$, then the
application $f\,C$ produces type $T$ in $\Delta$. If $C$ produces type $T$ in the context
$S :: \Delta$ obtained from $\Delta$ by adding a new leading variable of type $S$, then the
abstraction $\lambda C$ produces type $S \Rightarrow T$ in $\Delta$. In every rule the hole keeps
type $A$ in context $\Gamma$. -/
inductive TmCtx {Base : Type u} (Γ : List (Ty Base)) (A : Ty Base) :
    (Δ : List (Ty Base)) → (B : Ty Base) → Type u where
  | hole : TmCtx Γ A Γ A
  | appFun {Δ : List (Ty Base)} {B C : Ty Base}
      (ctx : TmCtx Γ A Δ (B ⇒ C)) (a : Tm Δ B) : TmCtx Γ A Δ C
  | appArg {Δ : List (Ty Base)} {B C : Ty Base}
      (f : Tm Δ (B ⇒ C)) (ctx : TmCtx Γ A Δ B) : TmCtx Γ A Δ C
  | lam {Δ : List (Ty Base)} {B C : Ty Base}
      (ctx : TmCtx Γ A (B :: Δ) C) : TmCtx Γ A Δ (B ⇒ C)

namespace TmCtx

/-- **Plugging a term into an STLC context.** Let $E$ be a typed one-hole context whose hole
has type $A$ in variable context $\Gamma$ and which produces a term of type $B$ in variable
context $\Delta$. For a term $t$ of type $A$ in $\Gamma$, the plugged term $E[t]$ of type $B$
in $\Delta$ is defined by recursion on $E$: $[\,][t] = t$, $(E\,a)[t] = E[t]\,a$,
$(f\,E)[t] = f\,E[t]$ and $(\lambda.\,E)[t] = \lambda.\,E[t]$, where $[\,]$ is the bare hole,
$E\,a$ applies $E$ to a term $a$, $f\,E$ applies a term $f$ to $E$, and $\lambda.\,E$ puts $E$
under a lambda. No renaming is applied, so a lambda above the hole may bind free variables
of $t$. -/
def plug {Δ : List (Ty Base)} {B : Ty Base} : TmCtx Γ A Δ B → Tm Γ A → Tm Δ B
  | .hole, t => t
  | .appFun C a, t => .app (plug C t) a
  | .appArg f C, t => .app f (plug C t)
  | .lam C, t => .lam (plug C t)

@[simp]
theorem plug_hole (t : Tm Γ A) : plug .hole t = t := rfl

@[simp]
theorem plug_appFun (C : TmCtx Γ A Δ (B ⇒ C)) (a : Tm Δ B) (t : Tm Γ A) :
    plug (.appFun C a) t = .app (plug C t) a := rfl

@[simp]
theorem plug_appArg (f : Tm Δ (B ⇒ C)) (C : TmCtx Γ A Δ B) (t : Tm Γ A) :
    plug (.appArg f C) t = .app f (plug C t) := rfl

@[simp]
theorem plug_lam (C : TmCtx Γ A (B :: Δ) C) (t : Tm Γ A) :
    plug (.lam C) t = .lam (plug C t) := rfl

/-- **Composition of STLC contexts.** Let $E_2$ be a typed one-hole context whose hole has
type $B$ in variable context $\Delta$ and which produces a term of type $C$ in context
$\Theta$, and let $E_1$ be one whose hole has type $A$ in context $\Gamma$ and which produces
a term of type $B$ in $\Delta$. The composite $E_2 \circ E_1$, with hole of type $A$ in
$\Gamma$ and result of type $C$ in $\Theta$, replaces the hole of $E_2$ by $E_1$; by
recursion on $E_2$: $[\,] \circ E_1 = E_1$, $(E_2\,a) \circ E_1 = (E_2 \circ E_1)\,a$,
$(f\,E_2) \circ E_1 = f\,(E_2 \circ E_1)$ and
$(\lambda.\,E_2) \circ E_1 = \lambda.\,(E_2 \circ E_1)$, where $[\,]$ is the bare hole and
$E\,a$, $f\,E$, $\lambda.\,E$ apply a context $E$ to a term $a$, apply a term $f$ to $E$, and
put $E$ under a lambda. -/
def comp {Δ Θ : List (Ty Base)} {B C : Ty Base} :
    TmCtx Δ B Θ C → TmCtx Γ A Δ B → TmCtx Γ A Θ C
  | .hole, inner => inner
  | .appFun outer a, inner => .appFun (comp outer inner) a
  | .appArg f outer, inner => .appArg f (comp outer inner)
  | .lam outer, inner => .lam (comp outer inner)

@[simp]
theorem hole_comp (C : TmCtx Γ A Δ B) : comp .hole C = C := rfl

@[simp]
theorem comp_hole (C : TmCtx Γ A Δ B) : comp C .hole = C := by
  induction C <;> simp [comp, *]

/-- **Plugging into a composite STLC context.** Let $E_2$ be a typed one-hole context whose
hole has type $B$ in variable context $\Delta$ and which produces a term of type $C$ in
context $\Theta$, and let $E_1$ be one whose hole has type $A$ in context $\Gamma$ and which
produces a term of type $B$ in $\Delta$. Then for every term $t$ of type $A$ in $\Gamma$,
$(E_2 \circ E_1)[t] = E_2[E_1[t]]$. -/
theorem plug_comp (outer : TmCtx Δ B Θ C) (inner : TmCtx Γ A Δ B) (t : Tm Γ A) :
    plug (comp outer inner) t = plug outer (plug inner t) := by
  induction outer <;> simp [comp, plug, *]

/-- **Associativity of composition of STLC contexts.** Let $E_1$ be a typed one-hole context
whose hole has type $A$ in variable context $\Gamma$ and which produces a term of type $B$ in
context $\Delta$, $E_2$ one with hole of type $B$ in $\Delta$ producing type $C$ in $\Theta$,
and $E_3$ one with hole of type $C$ in $\Theta$ producing type $D$ in $\Xi$. Then
$(E_3 \circ E_2) \circ E_1 = E_3 \circ (E_2 \circ E_1)$. -/
theorem comp_assoc (outer : TmCtx Θ C Ξ D) (middle : TmCtx Δ B Θ C)
    (inner : TmCtx Γ A Δ B) :
    comp (comp outer middle) inner = comp outer (comp middle inner) := by
  induction outer <;> simp [comp, *]

/-- **Semantic equality is a congruence for typed contexts.** Fix an interpretation $I$ of the
base types. Let $t$ and $u$ be terms of type $A$ in variable context $\Gamma$ that denote the same
value in $I$ under every semantic environment. Then for every typed one-hole context $C$ whose
hole has type $A$ in context $\Gamma$ and which produces a term of type $B$ in context $\Delta$, the
terms $C[t]$ and $C[u]$ obtained by plugging $t$ and $u$ into the hole also denote the same value
in $I$ under every semantic environment. -/
theorem semEq {I : Base → Type v} (C : TmCtx Γ A Δ B) {t u : Tm Γ A}
    (h : SemEq I t u) : SemEq I (plug C t) (plug C u) := by
  induction C with
  | hole => exact h
  | appFun C a ih => exact SemEq.app ih (SemEq.refl I a)
  | appArg f C ih => exact SemEq.app (SemEq.refl I f) ih
  | lam C ih => exact SemEq.lam ih

end TmCtx

/-- **Model equality of STLC terms.** Two terms $t$ and $u$ of type $A$ in variable
context $\Gamma$ are model-equal when, for every interpretation $I$ of the base types by types
in the same universe as the type of base types, they are semantically equal in $I$: with
function types interpreted as full function spaces, the denotations of $t$ and $u$ agree at
every semantic environment for $\Gamma$.

Unlike semantic equality in a fixed interpretation, this relation does not choose a particular
model. -/
def ModelEq (t u : Tm Γ A) : Prop :=
  ∀ I : Base → Type u, SemEq I t u

namespace ModelEq

theorem refl (t : Tm Γ A) : ModelEq t t := fun I ↦ SemEq.refl I t

theorem symm {t u : Tm Γ A} (h : ModelEq t u) : ModelEq u t :=
  fun I ↦ (h I).symm

theorem trans {t u w : Tm Γ A} (htu : ModelEq t u) (huw : ModelEq u w) :
    ModelEq t w := fun I ↦ (htu I).trans (huw I)

/-- **Model equality is a congruence for STLC contexts.** Let $E$ be a typed one-hole context
whose hole has type $A$ in variable context $\Gamma$ and which produces a term of type $B$ in
context $\Delta$. If two terms $t$ and $u$ of type $A$ in $\Gamma$ are model-equal, then
$E[t]$ and $E[u]$ are model-equal. -/
theorem context (C : TmCtx Γ A Δ B) {t u : Tm Γ A} (h : ModelEq t u) :
    ModelEq (C.plug t) (C.plug u) := fun I ↦ C.semEq (h I)

/-- **Model-independent beta equality.** For every term $b$ of type $B$ in the variable
context $\Gamma$ extended by a newest variable of type $A$, and every term $a$ of type $A$ in
$\Gamma$, the application $(\lambda.\,b)\,a$ is model-equal to $b[a]$, the result of
substituting $a$ for the newest variable of $b$. -/
theorem beta (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    ModelEq (.app (.lam body) a) (Tm.instantiate body a) :=
  fun I ↦ SemEq.beta I body a

/-- **Model-independent eta equality.** For every term $f$ of type $A \Rightarrow B$ in
variable context $\Gamma$, the term $\lambda.\,(f^{\uparrow}\,x_0)$ is model-equal to $f$,
where $f^{\uparrow}$ is $f$ weakened by a newest variable of type $A$ and $x_0$ is that
variable. -/
theorem eta (f : Tm Γ (A ⇒ B)) :
    ModelEq (.lam (.app (Tm.weaken f) (.var .zero))) f :=
  fun I ↦ SemEq.eta I f

/-- **Beta equality inside an STLC context.** Let $E$ be a typed one-hole context whose hole
has type $B$ in variable context $\Gamma$ and which produces a term of type $C$ in context
$\Delta$. For every term $b$ of type $B$ in $\Gamma$ extended by a newest variable of type
$A$, and every term $a$ of type $A$ in $\Gamma$, the term $E[(\lambda.\,b)\,a]$ is
model-equal to $E[b[a]]$, where $b[a]$ is the result of substituting $a$ for the newest
variable of $b$. -/
theorem context_beta (C : TmCtx Γ B Δ C) (body : Tm (A :: Γ) B) (a : Tm Γ A) :
    ModelEq (C.plug (.app (.lam body) a)) (C.plug (Tm.instantiate body a)) :=
  context C (beta body a)

/-- **Eta equality inside an STLC context.** Let $E$ be a typed one-hole context whose hole
has type $A \Rightarrow B$ in variable context $\Gamma$ and which produces a term of type $C$
in context $\Delta$. For every term $f$ of type $A \Rightarrow B$ in $\Gamma$, the term
$E[\lambda.\,(f^{\uparrow}\,x_0)]$ is model-equal to $E[f]$, where $f^{\uparrow}$ is $f$
weakened by a newest variable of type $A$ and $x_0$ is that variable. -/
theorem context_eta (C : TmCtx Γ (A ⇒ B) Δ C) (f : Tm Γ (A ⇒ B)) :
    ModelEq (C.plug (.lam (.app (Tm.weaken f) (.var .zero))) ) (C.plug f) :=
  context C (eta f)

theorem equivalence : Equivalence (@ModelEq Base A Γ) := ⟨refl, symm, trans⟩

end ModelEq

end Cslib.Languages.LambdaCalculus.Stlc
