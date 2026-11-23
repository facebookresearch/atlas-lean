/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Call-by-value CPS translation of the simply typed lambda calculus
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

/-!
# Call-by-value CPS translation and its denotational correctness

The call-by-value continuation-passing-style translation of Plotkin
(*Call-by-name, call-by-value and the λ-calculus*, TCS 1, 1975), in the
typed form of Meyer and Wand (*Continuation semantics in typed
lambda-calculi*, Logics of Programs 1985), on the intrinsically typed de
Bruijn STLC of `../DeBruijn/Stlc/`. For a fixed answer type `R`:

* types: `⟦b⟧ = b` and `⟦A → B⟧ = ⟦A⟧ → (⟦B⟧ → R) → R`; a term of type `A`
  becomes a computation of type `(⟦A⟧ → R) → R` (`compTy`);
* terms: `⟦x⟧ = λk. k x`, `⟦λx. M⟧ = λk. k (λx. ⟦M⟧)`, and
  `⟦M N⟧ = λk. ⟦M⟧ (λm. ⟦N⟧ (λn. m n k))`.

Because terms are intrinsically typed, `cps` is type preserving by
construction: it maps `Tm Γ A` to `Tm (Γ.map (cpsTy R)) (compTy R A)`.

Correctness is the Meyer–Wand theorem for the set-theoretic semantics
(`Tm.denote`): for related environments, the denotation of `⟦M⟧` applied to
any continuation `k` is `k v'` for a value `v'` related to the denotation of
`M`, where `Rel` is the logical relation that is equality at base types
(`cps_correct`). For terms of base type this says that running the
translation with continuation `k` returns `k` of the original value
(`cps_denote_base`), and with the identity continuation it returns the
original value (`cps_denote_base_id`). Pure STLC has no closed terms of base
type, so these are stated for open terms in related environments.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS

open scoped CslibStlc

universe u v

variable {Base : Type u}

/-- **Call-by-value CPS translation of types.** For a fixed answer type $R$, the translation
$\overline{A}$ of a simple type $A$ is defined by recursion on $A$: $\overline{b} = b$ for a base
type $b$, and $\overline{A \to B} = \overline{A} \to ((\overline{B} \to R) \to R)$. -/
def cpsTy (R : Ty Base) : Ty Base → Ty Base
  | .base b => .base b
  | .arr A B => cpsTy R A ⇒ ((cpsTy R B ⇒ R) ⇒ R)

/-- **CPS computation type.** For an answer type $R$ and a simple type $A$, the type of CPS
computations returning a value of type $A$ is $(\overline{A} \to R) \to R$, where $\overline{A}$
is the call-by-value CPS translation of $A$ for answer type $R$. -/
abbrev compTy (R : Ty Base) (A : Ty Base) : Ty Base :=
  (cpsTy R A ⇒ R) ⇒ R

@[simp] theorem cpsTy_base (R : Ty Base) (b : Base) : cpsTy R (.base b) = .base b := rfl

@[simp] theorem cpsTy_arr (R A B : Ty Base) :
    cpsTy R (A ⇒ B) = cpsTy R A ⇒ compTy R B := rfl

variable (R : Ty Base)

/-- **CPS translation of variables.** Fix an answer type $R$ and write $\overline{A}$ for the
call-by-value CPS translation of a type $A$. A de Bruijn variable of type $A$ in a context
$A_1, \ldots, A_n$ is sent to the variable at the same position in the translated context
$\overline{A_1}, \ldots, \overline{A_n}$, which has type $\overline{A}$. -/
def cpsVar : {Γ : List (Ty Base)} → {A : Ty Base} →
    Var Γ A → Var (Γ.map (cpsTy R)) (cpsTy R A)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (cpsVar x)

/-- **Call-by-value CPS translation of terms.** Fix an answer type $R$ and write $\overline{A}$
for the call-by-value CPS translation of a type $A$ and $\overline{\Gamma}$ for the context
obtained by translating each type of a context $\Gamma$. A term $M$ of type $A$ in context
$\Gamma$ is sent to a term $\overline{M}$ of type $(\overline{A} \to R) \to R$ in context
$\overline{\Gamma}$, defined by recursion on $M$ by $\overline{x} = \lambda k.\,k\,x$,
$\overline{\lambda x.\,M} = \lambda k.\,k\,(\lambda x.\,\overline{M})$ and
$\overline{M\,N} = \lambda k.\,\overline{M}\,(\lambda m.\,\overline{N}\,(\lambda n.\,m\,n\,k))$,
where $k$, $m$ and $n$ are fresh variables. -/
def cps : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm (Γ.map (cpsTy R)) (compTy R A)
  | _, _, .var x => .lam (.app (.var .zero) (.var (.succ (cpsVar R x))))
  | _, _, .lam body => .lam (.app (.var .zero) (Tm.weaken (.lam (cps body))))
  | _, _, .app f a =>
      .lam (.app (Tm.weaken (cps f))
        (.lam (.app (Tm.weaken (Tm.weaken (cps a)))
          (.lam (.app (.app (.var (.succ .zero)) (.var .zero))
            (.var (.succ (.succ .zero))))))))

section Equations

variable {Γ : List (Ty Base)} {A B : Ty Base}

@[simp] theorem cpsVar_zero : cpsVar R (.zero : Var (A :: Γ) A) = .zero := rfl

@[simp] theorem cpsVar_succ (x : Var Γ A) :
    cpsVar R (.succ x : Var (B :: Γ) A) = .succ (cpsVar R x) := rfl

@[simp] theorem cps_var (x : Var Γ A) :
    cps R (.var x) = .lam (.app (.var .zero) (.var (.succ (cpsVar R x)))) := rfl

@[simp] theorem cps_lam (body : Tm (A :: Γ) B) :
    cps R (.lam body) =
      .lam (.app (.var .zero) (Tm.weaken (.lam (cps R body)))) := rfl

@[simp] theorem cps_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    cps R (.app f a) =
      .lam (.app (Tm.weaken (cps R f))
        (.lam (.app (Tm.weaken (Tm.weaken (cps R a)))
          (.lam (.app (.app (.var (.succ .zero)) (.var .zero))
            (.var (.succ (.succ .zero)))))))) := rfl

end Equations

variable {I : Base → Type v}

/-- **Logical relation for the CPS translation.** Fix an answer type $R$ and an interpretation
$I$ of the base types; write $D(A)$ for the set interpreting a simple type $A$ under $I$ and
$\overline{A}$ for the call-by-value CPS translation of $A$. The relation $a \sim_A a'$ between
$a \in D(A)$ and $a' \in D(\overline{A})$ is defined by recursion on $A$: at a base type $b$,
$a \sim_b a'$ means $a = a'$; at a function type, $f \sim_{A \to B} f'$ means that for all
$a \sim_A a'$ there is a $b' \in D(\overline{B})$ with $f(a) \sim_B b'$ and $f'(a')(k) = k(b')$
for every continuation $k \in D(\overline{B} \to R)$. -/
def Rel (I : Base → Type v) : (A : Ty Base) → Ty.denote I A → Ty.denote I (cpsTy R A) → Prop
  | .base _, a, a' => a = a'
  | .arr A B, f, f' => ∀ a a', Rel I A a a' →
      ∃ b', Rel I B (f a) b' ∧ ∀ k, f' a' k = k b'

@[simp] theorem rel_base (b : Base) (a : I b) (a' : Ty.denote I (cpsTy R (.base b))) :
    Rel R I (.base b) a a' ↔ a = a' := Iff.rfl

theorem rel_arr (A B : Ty Base) (f : Ty.denote I (A ⇒ B))
    (f' : Ty.denote I (cpsTy R (A ⇒ B))) :
    Rel R I (A ⇒ B) f f' ↔ ∀ a a', Rel R I A a a' →
      ∃ b', Rel R I B (f a) b' ∧ ∀ k, f' a' k = k b' := Iff.rfl

/-- **Related environments.** Fix an answer type $R$ and an interpretation $I$ of the base types,
and write $\overline{\Gamma}$ for the context obtained by translating each type of a context
$\Gamma$ by the call-by-value CPS translation. An environment $\eta$ for $\Gamma$ and an
environment $\eta'$ for $\overline{\Gamma}$ are related when, for every variable $x$ of type $A$
in $\Gamma$, the value $\eta(x)$ is related at type $A$, by the CPS logical relation, to the value
that $\eta'$ assigns to the variable at the same position in $\overline{\Gamma}$. -/
def EnvRel {Γ : List (Ty Base)} (η : Env I Γ) (η' : Env I (Γ.map (cpsTy R))) : Prop :=
  ∀ {A} (x : Var Γ A), Rel R I A (η x) (η' (cpsVar R x))

theorem EnvRel.cons {Γ : List (Ty Base)} {A : Ty Base} {η : Env I Γ}
    {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η') {a : Ty.denote I A}
    {a' : Ty.denote I (cpsTy R A)} (ha : Rel R I A a a') :
    EnvRel R (Env.cons a η) (Env.cons (Γ := Γ.map (cpsTy R)) a' η') := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hη x

/-- **Denotational correctness of the CPS translation (Meyer–Wand).** Fix an answer type $R$
and an interpretation $I$ of the base types; write $D(A)$ for the set interpreting a type $A$,
$\overline{A}$, $\overline{\Gamma}$ and $\overline{t}$ for the call-by-value CPS translations of
types, contexts and terms, and $[t]_\eta$ for the denotation of a term $t$ in an environment
$\eta$. Let $t$ be a term of type $A$ in context $\Gamma$, and let $\eta$ and $\eta'$ be related
environments for $\Gamma$ and $\overline{\Gamma}$. Then there is a value $v' \in D(\overline{A})$,
related to $[t]_\eta$ by the CPS logical relation at $A$, such that $[\overline{t}]_{\eta'}(k) =
k(v')$ for every continuation $k \colon D(\overline{A}) \to D(R)$. -/
theorem cps_correct {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) {η : Env I Γ}
    {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η') :
    ∃ v', Rel R I A (Tm.denote I t η) v' ∧
      ∀ k, Tm.denote I (cps R t) η' k = k v' := by
  induction t with
  | var x => exact ⟨η' (cpsVar R x), hη x, fun _ => rfl⟩
  | @lam A B Γ body ih =>
      refine ⟨Tm.denote I (.lam (cps R body)) η', ?_, ?_⟩
      · intro a a' ha
        exact ih (hη.cons R ha)
      · intro k
        exact congrArg k (Tm.denote_weaken I (.lam (cps R body)) k η')
  | @app A B Γ f a ihf iha =>
      obtain ⟨f', hf, hfk⟩ := ihf hη
      obtain ⟨a', ha, hak⟩ := iha hη
      obtain ⟨b', hb, hbk⟩ := hf _ _ ha
      refine ⟨b', hb, fun k => ?_⟩
      have hwa : ∀ m : Ty.denote I (cpsTy R (A ⇒ B)),
          Tm.denote I (Tm.weaken (B := cpsTy R (A ⇒ B)) (Tm.weaken (B := cpsTy R B ⇒ R) (cps R a)))
            (Env.cons m (Env.cons k η')) = Tm.denote I (cps R a) η' := fun m =>
        (Tm.denote_weaken I _ m (Env.cons k η')).trans (Tm.denote_weaken I (cps R a) k η')
      have hstep : Tm.denote I (cps R (.app f a)) η' k =
          Tm.denote I (cps R f) η' (fun m => Tm.denote I (cps R a) η' (fun n => m n k)) := by
        refine (congrFun (Tm.denote_weaken I (cps R f) k η') _).trans ?_
        refine congrArg (Tm.denote I (cps R f) η') (funext fun m => ?_)
        exact congrFun (hwa m) _
      exact hstep.trans ((hfk _).trans ((hak _).trans (hbk k)))

/-- **CPS translation at a base type.** Fix an answer type $R$ and an interpretation $I$ of the
base types; write $D(A)$ for the set interpreting a type $A$, $\overline{\Gamma}$ and
$\overline{t}$ for the call-by-value CPS translations of contexts and terms, and $[t]_\eta$ for
the denotation of a term $t$ in an environment $\eta$. Let $t$ be a term of base type $b$ in
context $\Gamma$, and let $\eta$ and $\eta'$ be related environments for $\Gamma$ and
$\overline{\Gamma}$. Then $[\overline{t}]_{\eta'}(k) = k([t]_\eta)$ for every continuation
$k \colon I(b) \to D(R)$. -/
theorem cps_denote_base {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cpsTy R))} (hη : EnvRel R η η')
    (k : Ty.denote I (cpsTy R (.base b) ⇒ R)) :
    Tm.denote I (cps R t) η' k = k (Tm.denote I t η) := by
  obtain ⟨v', hv, hk⟩ := cps_correct R t hη
  rw [hk k]
  exact congrArg k hv.symm

/-- **CPS translation at a base type with the identity continuation.** Fix an interpretation $I$
of the base types, let $t$ be a term of base type $b$ in context $\Gamma$, and take the answer
type to be $b$; write $\overline{\Gamma}$ and $\overline{t}$ for the call-by-value CPS
translations of $\Gamma$ and $t$, and $[t]_\eta$ for the denotation of $t$ in an environment
$\eta$. If $\eta$ and $\eta'$ are related environments for $\Gamma$ and $\overline{\Gamma}$, then
$[\overline{t}]_{\eta'}(\mathrm{id}) = [t]_\eta$, where $\mathrm{id}$ is the identity on $I(b)$. -/
theorem cps_denote_base_id {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cpsTy (.base b)))} (hη : EnvRel (.base b) η η') :
    Tm.denote I (cps (.base b) t) η' id = Tm.denote I t η :=
  cps_denote_base (.base b) t hη id

end Cslib.Languages.LambdaCalculus.Stlc.CPS
