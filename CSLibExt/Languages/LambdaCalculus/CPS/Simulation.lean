/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Operational correctness of the CPS translation
-/
module

public import CSLibExt.Languages.LambdaCalculus.CPS.Translation
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.BigStep
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.SubstitutionLaws

/-!
# Operational correctness of the call-by-value CPS translation

Plotkin's simulation theorem (*Call-by-name, call-by-value and the λ-calculus*,
TCS 1, 1975, Theorem 2), in big-step form, for the typed translation of
`Translation.lean` and the call-by-value big-step semantics `Stlc.Eval` of
`../DeBruijn/Stlc/BigStep.lean`: if `M ⇓ λx. N`, then for every continuation
value `K`, the program `⟦M⟧ K` evaluates to `w` exactly when `K (λx. ⟦N⟧)`
does (`cps_simulation`). Here `λx. ⟦N⟧` is Plotkin's value translation `Ψ`.

The proof needs the translation to commute with renaming (`cps_rename`) and
with substitution of values and variables (`cps_subst`, `cps_instantiate`);
`PsiRel` relates a value or variable to its translation `Ψ`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS

open scoped CslibStlc

universe u

variable {Base : Type u} (R : Ty Base)

/-- **Translated renaming.** Fix an answer type $R$ and write $\llbracket \Gamma \rrbracket$ for the
context obtained by applying the call-by-value CPS type translation to every entry of $\Gamma$. A
renaming $\rho$ from $\Gamma$ to $\Delta$ induces the renaming from $\llbracket \Gamma \rrbracket$
to $\llbracket \Delta \rrbracket$ that sends the translation of each variable $x$ of $\Gamma$ (the
variable at the same position) to the translation of $\rho(x)$. -/
def cpsRen : {Γ Δ : List (Ty Base)} → Ren Γ Δ → Ren (Γ.map (cpsTy R)) (Δ.map (cpsTy R))
  | [], _, _, _, x => nomatch x
  | _ :: _, _, ρ, _, .zero => cpsVar R (ρ .zero)
  | _ :: _, _, ρ, _, .succ y => cpsRen (fun x => ρ (.succ x)) y

variable {R}
variable {Γ Δ : List (Ty Base)} {A B : Ty Base}

@[simp] theorem cpsRen_cpsVar (ρ : Ren Γ Δ) (x : Var Γ A) :
    cpsRen R ρ (cpsVar R x) = cpsVar R (ρ x) := by
  induction x generalizing Δ with
  | zero => rfl
  | succ x ih => exact ih (fun y => ρ (.succ y))

theorem cpsRen_succ (ρ : Ren Γ Δ) {T : Ty Base} (y : Var (Γ.map (cpsTy R)) T) :
    cpsRen R (fun x => (ρ x).succ (B := B)) y = (cpsRen R ρ y).succ := by
  induction Γ generalizing Δ with
  | nil => exact nomatch y
  | cons C Γ ih =>
      cases y with
      | zero => rfl
      | succ y => exact ih (fun x => ρ (.succ x)) y

theorem cpsRen_id {T : Ty Base} (y : Var (Γ.map (cpsTy R)) T) :
    cpsRen R (Var.id : Ren Γ Γ) y = y := by
  induction Γ with
  | nil => exact nomatch y
  | cons C Γ ih =>
      cases y with
      | zero => rfl
      | succ y =>
          change cpsRen R (fun x => (Var.id x).succ (B := C)) y = _
          rw [cpsRen_succ]
          exact congrArg Var.succ (ih y)

theorem cpsRen_lift (ρ : Ren Γ Δ) {T : Ty Base} (y : Var ((A :: Γ).map (cpsTy R)) T) :
    cpsRen R (Var.lift ρ) y = Var.lift (cpsRen R ρ) y := by
  cases y with
  | zero => rfl
  | succ y => exact cpsRen_succ ρ y

/-- **The call-by-value CPS translation commutes with renaming.** Fix an answer type $R$ and
write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts
(entrywise) and terms. For every renaming $\rho$ from a context $\Gamma$ to a context $\Delta$ and
every term $t$ of type $A$ in $\Gamma$, the translation of the renamed term $t[\rho]$ equals the
renaming of $\llbracket t \rrbracket$ along the translated renaming from
$\llbracket \Gamma \rrbracket$ to $\llbracket \Delta \rrbracket$, which sends the translation of
each variable $x$ of $\Gamma$ to the translation of $\rho(x)$. -/
theorem cps_rename (ρ : Ren Γ Δ) (t : Tm Γ A) :
    cps R (Tm.rename ρ t) = Tm.rename (cpsRen R ρ) (cps R t) := by
  induction t generalizing Δ with
  | var x => simp
  | @lam A B Γ body ih =>
      simp only [Tm.rename_lam, cps_lam, Tm.rename_app, Tm.rename_var, Var.lift_zero, ih]
      refine congrArg (fun t => Tm.lam (Tm.app (Tm.var Var.zero) t)) ?_
      refine Eq.trans ?_ (Tm.rename_weaken (cpsRen R ρ)
        (Tm.lam (cps R body) : Tm (Γ.map (cpsTy R)) (cpsTy R (A ⇒ B)))).symm
      exact congrArg Tm.weaken (congrArg Tm.lam (Tm.rename_congr (fun y => cpsRen_lift ρ y) _))
  | app f a ihf iha =>
      simp only [Tm.rename_lam, cps_app, Tm.rename_app, Tm.rename_var, ihf, iha]
      rw [Tm.rename_weaken, Tm.rename_weaken, Tm.rename_weaken]
      rfl

theorem cpsRen_weaken {T : Ty Base} (y : Var (Γ.map (cpsTy R)) T) :
    cpsRen R (fun x => Var.succ (B := B) x) y = y.succ :=
  (cpsRen_succ Var.id y).trans (congrArg Var.succ (cpsRen_id y))

/-- **The CPS translation commutes with weakening.** Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. For every term $t$ of type $A$ in a context $\Gamma$ and every type $B$, the translation
of the weakening of $t$ to the context $B, \Gamma$ is the weakening of $\llbracket t \rrbracket$ to
the context $\llbracket B \rrbracket, \llbracket \Gamma \rrbracket$. -/
theorem cps_weaken (t : Tm Γ A) :
    cps R (Tm.weaken (B := B) t) = Tm.weaken (cps R t) := by
  rw [Tm.weaken, cps_rename, Tm.weaken]
  exact Tm.rename_congr (fun y => cpsRen_weaken y) _

/-- **Plotkin's value translation $\Psi$.** Fix an answer type $R$, and write $A^*$ for the
call-by-value CPS translation of a type $A$, $\Gamma^*$ for the context obtained by translating
each type of a context $\Gamma$, and $\overline{M}$ for the CPS translation of a term $M$. The
relation $\Psi$ between terms of type $A$ in context $\Gamma$ and terms of type $A^*$ in context
$\Gamma^*$ holds in exactly two cases: a variable $x$ of $\Gamma$ is related to the variable at
the same position in $\Gamma^*$, and an abstraction $\lambda x.\, N$ is related to
$\lambda x.\, \overline{N}$. -/
inductive PsiRel : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm (Γ.map (cpsTy R)) (cpsTy R A) → Prop
  | var {Γ : List (Ty Base)} {A : Ty Base} (x : Var Γ A) : PsiRel (.var x) (.var (cpsVar R x))
  | lam {Γ : List (Ty Base)} {A B : Ty Base} (body : Tm (A :: Γ) B) :
      PsiRel (.lam body) (.lam (cps R body))

theorem PsiRel.weaken {v : Tm Γ A} {p : Tm (Γ.map (cpsTy R)) (cpsTy R A)}
    (h : PsiRel (R := R) v p) : PsiRel (R := R) (Tm.weaken (B := B) v) (Tm.weaken p) := by
  cases h with
  | var x => exact .var (.succ x)
  | lam body =>
      have := PsiRel.lam (R := R) (Tm.rename (Var.lift (Var.succ (B := B))) body)
      rw [cps_rename] at this
      refine (congrArg (PsiRel _) ?_).mp this
      change Tm.lam _ = Tm.rename _ (Tm.lam _)
      rw [Tm.rename_lam]
      exact congrArg Tm.lam (Tm.rename_congr (fun y => (cpsRen_lift _ y).trans (by
        cases y with
        | zero => rfl
        | succ y => exact congrArg Var.succ (cpsRen_weaken y))) _)

/-- **The CPS translation commutes with substitution of values and variables.** Fix an answer
type $R$ and write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types,
contexts (entrywise) and terms; for a variable $x$ of $\Gamma$, $\llbracket x \rrbracket$ is the
variable of $\llbracket \Gamma \rrbracket$ at the same position. Let $\sigma$ be a substitution from
$\Gamma$ to $\Delta$ and $\tau$ a substitution from $\llbracket \Gamma \rrbracket$ to
$\llbracket \Delta \rrbracket$ such that for every variable $x$ of $\Gamma$, the term
$\tau(\llbracket x \rrbracket)$ is related to $\sigma(x)$ by the value translation $\Psi$ (a
variable is related to the corresponding variable, $\lambda y. N$ to
$\lambda y. \llbracket N \rrbracket$). Then for every term $M$ in $\Gamma$, writing $M[\sigma]$
for the result of applying $\sigma$ to $M$, we have
$\llbracket M[\sigma] \rrbracket = \llbracket M \rrbracket[\tau]$. -/
theorem cps_subst (t : Tm Γ A) {σ : Sub Γ Δ} {τ : Sub (Γ.map (cpsTy R)) (Δ.map (cpsTy R))}
    (hτ : ∀ {B} (x : Var Γ B), PsiRel (R := R) (σ x) (τ (cpsVar R x))) :
    cps R (Tm.subst σ t) = Tm.subst τ (cps R t) := by
  induction t generalizing Δ with
  | var x =>
      have h := hτ x
      simp only [Tm.subst_var, cps_var, Tm.subst_lam, Tm.subst_app, Sub.lift_zero,
        Sub.lift_succ]
      revert h
      generalize σ x = s
      generalize τ (cpsVar R x) = p
      intro h
      cases h with
      | var y => rfl
      | lam body => rfl
  | @lam A B Γ body ih =>
      simp only [Tm.subst_lam, cps_lam, Tm.subst_app, Tm.subst_var, Sub.lift_zero]
      refine congrArg (fun t => Tm.lam (Tm.app (Tm.var Var.zero) t)) ?_
      refine Eq.trans ?_ (Tm.subst_lift_weaken τ
        (Tm.lam (cps R body) : Tm (Γ.map (cpsTy R)) (cpsTy R (A ⇒ B)))).symm
      have hlift : ∀ {C} (x : Var (A :: Γ) C),
          PsiRel (R := R) (Sub.lift σ x) (Sub.lift τ (cpsVar R x)) := by
        intro C x
        cases x with
        | zero => exact .var .zero
        | succ x => exact (hτ x).weaken
      exact congrArg Tm.weaken (congrArg Tm.lam (ih (Δ := A :: Δ)
        (τ := (Sub.lift (A := cpsTy R A) τ :
          Sub ((A :: Γ).map (cpsTy R)) ((A :: Δ).map (cpsTy R)))) hlift))
  | app f a ihf iha =>
      simp only [Tm.subst_lam, cps_app, Tm.subst_app, Tm.subst_var, ihf hτ, iha hτ]
      rw [Tm.subst_lift_weaken, Tm.subst_lift_weaken, Tm.subst_lift_weaken]
      rfl

/-- **The CPS translation commutes with instantiation by a value or variable.** Fix an answer
type $R$ and write $\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types,
contexts (entrywise) and terms. Let $N$ be a term of type $B$ in a context $A, \Gamma$, let $v$
be a term of type $A$ in $\Gamma$, and let $p$ be a term of type $\llbracket A \rrbracket$ in
$\llbracket \Gamma \rrbracket$ related to $v$ by the value translation $\Psi$ (a variable is related
to the corresponding variable, $\lambda x. M$ to $\lambda x. \llbracket M \rrbracket$). Writing
$N[u]$ for $N$ with its newest free variable replaced by $u$, we have
$\llbracket N[v] \rrbracket = \llbracket N \rrbracket[p]$. -/
theorem cps_instantiate (body : Tm (A :: Γ) B) {v : Tm Γ A}
    {p : Tm (Γ.map (cpsTy R)) (cpsTy R A)} (h : PsiRel (R := R) v p) :
    cps R (Tm.instantiate body v) = Tm.instantiate (cps R body) p := by
  refine cps_subst body fun x => ?_
  cases x with
  | zero => exact h
  | succ x => exact .var x

/-- **The value translation preserves values.** Fix an answer type $R$. If a term $v$ of type $A$
in context $\Gamma$ is related by Plotkin's value translation $\Psi$ to a term $p$ (of the
translated type in the translated context), and $v$ is a value, that is, a $\lambda$-abstraction,
then $p$ is a value. -/
theorem PsiRel.value {v : Tm Γ A} {p : Tm (Γ.map (cpsTy R)) (cpsTy R A)}
    (h : PsiRel (R := R) v p) (hv : Value v) : Value p := by
  cases h with
  | var x => exact nomatch hv
  | lam body => exact .lam _

section Eval

variable {Ξ : List (Ty Base)} {C D : Ty Base}

/-- **A β-redex with a value argument evaluates as its contractum.** Let $N$ be a term of type $D$
in a context $C, \Xi$ and let $v$ be a value of type $C$ in $\Xi$. Writing $N[v]$ for $N$ with its
newest free variable replaced by $v$, for every term $w$ of type $D$ the application
$(\lambda x. N)\, v$ evaluates to $w$ under call-by-value big-step evaluation if and only if $N[v]$
evaluates to $w$. -/
theorem eval_app_lam_iff {body : Tm (C :: Ξ) D} {v : Tm Ξ C} (hv : Value v) {w : Tm Ξ D} :
    Eval (.app (.lam body) v) w ↔ Eval (Tm.instantiate body v) w := by
  constructor
  · intro h
    cases h with
    | app hf ha hb =>
        cases hf
        cases Eval.deterministic ha (Eval.value_self hv)
        exact hb
  · intro h
    exact .app (.lam body) (Eval.value_self hv) h

/-- **Evaluation of an application depends on the function only through its results.** Let $F$
and $F'$ be terms of type $C \to D$ in a context $\Xi$ such that, for every term $u$, $F$ evaluates
to $u$ under call-by-value big-step evaluation if and only if $F'$ does. Then for every term $a$ of
type $C$ and every term $w$ of type $D$ in $\Xi$, the application $F\, a$ evaluates to $w$ if and
only if $F'\, a$ evaluates to $w$. -/
theorem eval_app_congr_fun {F F' : Tm Ξ (C ⇒ D)} (h : ∀ u, Eval F u ↔ Eval F' u)
    {a : Tm Ξ C} {w : Tm Ξ D} : Eval (.app F a) w ↔ Eval (.app F' a) w := by
  constructor
  · intro h'
    cases h' with
    | app hf ha hb => exact .app ((h _).mp hf) ha hb
  · intro h'
    cases h' with
    | app hf ha hb => exact .app ((h _).mpr hf) ha hb

end Eval

section Instantiate

variable {Ξ : List (Ty Base)} {X Y Z : Ty Base}

/-! The administrative reductions of the translation, at generic types. -/

/-- **Instantiating a return to the continuation.** Let $V$ be a term of type $X$ and $K$ a term
of type $X \to Z$ in a context $\Xi$. In the context $X \to Z, \Xi$, let $k$ be the newest
variable (of type $X \to Z$) and $V'$ the weakening of $V$. Replacing $k$ by $K$ in the term
$k\, V'$ gives $K\, V$. -/
theorem instantiate_ret (V : Tm Ξ X) (K : Tm Ξ (X ⇒ Z)) :
    Tm.instantiate (.app (.var .zero) (Tm.weaken V)) K = .app K V := by
  simp [Tm.instantiate]

theorem instantiate_app₁ (F : Tm Ξ (((X ⇒ ((Y ⇒ Z) ⇒ Z)) ⇒ Z) ⇒ Z))
    (N : Tm Ξ ((X ⇒ Z) ⇒ Z)) (K : Tm Ξ (Y ⇒ Z)) :
    Tm.instantiate (.app (Tm.weaken F)
        (.lam (.app (Tm.weaken (Tm.weaken N))
          (.lam (.app (.app (.var (.succ .zero)) (.var .zero)) (.var (.succ (.succ .zero))))))))
      K =
    .app F (.lam (.app (Tm.weaken N)
      (.lam (.app (.app (.var (.succ .zero)) (.var .zero)) (Tm.weaken (Tm.weaken K)))))) := by
  simp [Tm.instantiate, Tm.subst_lift_weaken]
  rfl

theorem instantiate_app₂ (N : Tm Ξ ((X ⇒ Z) ⇒ Z)) (P : Tm Ξ (X ⇒ ((Y ⇒ Z) ⇒ Z)))
    (K : Tm Ξ (Y ⇒ Z)) :
    Tm.instantiate (.app (Tm.weaken N)
        (.lam (.app (.app (.var (.succ .zero)) (.var .zero)) (Tm.weaken (Tm.weaken K))))) P =
    .app N (.lam (.app (.app (Tm.weaken P) (.var .zero)) (Tm.weaken K))) := by
  simp [Tm.instantiate, Tm.subst_lift_weaken]

theorem instantiate_app₃ (P : Tm Ξ (X ⇒ ((Y ⇒ Z) ⇒ Z))) (Q : Tm Ξ X) (K : Tm Ξ (Y ⇒ Z)) :
    Tm.instantiate (.app (.app (Tm.weaken P) (.var .zero)) (Tm.weaken K)) Q =
      .app (.app P Q) K := by
  simp [Tm.instantiate]

end Instantiate

/-- **Plotkin's simulation theorem, big-step form.** Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. If a term $M$ of type $A$ in a context $\Gamma$ evaluates to $V$ under call-by-value
big-step evaluation, then there is a term $p$ related to $V$ by the value translation $\Psi$ (a
variable is related to the corresponding variable, $\lambda x. N$ to
$\lambda x. \llbracket N \rrbracket$) such that for every value $K$ of type
$\llbracket A \rrbracket \to R$ in $\llbracket \Gamma \rrbracket$ and every term $w$, the
application $\llbracket M \rrbracket\, K$ evaluates to $w$ if and only if $K\, p$ evaluates
to $w$. -/
theorem cps_simulation {M V : Tm Γ A} (h : Eval M V) :
    ∃ p, PsiRel (R := R) V p ∧ ∀ (K : Tm (Γ.map (cpsTy R)) (cpsTy R A ⇒ R)), Value K →
      ∀ w, (Eval (.app (cps R M) K) w ↔ Eval (.app K p) w) := by
  induction h with
  | lam body =>
      refine ⟨_, .lam body, fun K hK w => (eval_app_lam_iff hK).trans ?_⟩
      exact iff_of_eq (congrArg (Eval · w) (instantiate_ret (Tm.lam (cps R body)) K))
  | @app A B f a bf va v hf ha hb ihf iha ihb =>
      obtain ⟨pf, hpf, hsimf⟩ := ihf
      obtain ⟨pa, hpa, hsima⟩ := iha
      obtain ⟨pb, hpb, hsimb⟩ := ihb
      cases hpf
      refine ⟨pb, hpb, fun K hK w => ?_⟩
      have hpaV : Value pa := hpa.value ha.value
      refine (eval_app_lam_iff hK).trans ?_
      refine (iff_of_eq (congrArg (Eval · w) (instantiate_app₁ (cps R f) (cps R a) K))).trans ?_
      refine (hsimf _ (.lam _) w).trans ?_
      refine (eval_app_lam_iff (.lam _)).trans ?_
      refine (iff_of_eq (congrArg (Eval · w)
        (instantiate_app₂ (cps R a) (Tm.lam (cps R bf)) K))).trans ?_
      refine (hsima _ (.lam _) w).trans ?_
      refine (eval_app_lam_iff hpaV).trans ?_
      refine (iff_of_eq (congrArg (Eval · w)
        (instantiate_app₃ (Tm.lam (cps R bf)) pa K))).trans ?_
      refine (eval_app_congr_fun (fun u => eval_app_lam_iff hpaV)).trans ?_
      refine (iff_of_eq (congrArg (fun t => Eval (.app t K) w)
        (cps_instantiate bf hpa).symm)).trans ?_
      exact hsimb K hK w

/-- **Simulation for terms evaluating to an abstraction.** Fix an answer type $R$ and write
$\llbracket \cdot \rrbracket$ for the call-by-value CPS translation of types, contexts (entrywise)
and terms. If a term $M$ of type $A \to B$ in a context $\Gamma$ evaluates to $\lambda x. N$ under
call-by-value big-step evaluation, then for every value $K$ of type
$\llbracket A \to B \rrbracket \to R$ in $\llbracket \Gamma \rrbracket$ and every term $w$ of type
$R$, the application $\llbracket M \rrbracket\, K$ evaluates to $w$ if and only if
$K\, (\lambda x. \llbracket N \rrbracket)$ evaluates to $w$. -/
theorem cps_simulation_lam {M : Tm Γ (A ⇒ B)} {body : Tm (A :: Γ) B} (h : Eval M (.lam body))
    (K : Tm (Γ.map (cpsTy R)) (cpsTy R (A ⇒ B) ⇒ R)) (hK : Value K) (w : Tm _ R) :
    Eval (.app (cps R M) K) w ↔ Eval (.app K (.lam (cps R body))) w := by
  obtain ⟨p, hp, hsim⟩ := cps_simulation (R := R) h
  cases hp
  exact hsim K hK w

end Cslib.Languages.LambdaCalculus.Stlc.CPS
