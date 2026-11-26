/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Substitution
public import Mathlib.Logic.Relation
public import Cslib.Foundations.Relation.Defs

/-!
# Call-by-value dynamics for the extended simply typed lambda calculus

The eager, left-to-right call-by-value small-step semantics of the calculus with unit, products,
sums, booleans and `let`: values (`Value`), one-step reduction (`Step`) and its reflexive
transitive closure (`Steps`).

`Step` relates two terms of the same type in the same context, so preservation holds by
construction: each reduction rule is accepted only because its two sides have the same type,
which is the content that a separate preservation theorem would state. Type safety therefore
consists of progress for closed terms (`Step.progress`) together with this intrinsic closure of
`Step` under typing, and the multi-step safety corollaries in
`CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Safety` apply progress at every
reachable term.

The file also states that values do not reduce, the canonical forms of closed values at function,
product, sum, boolean and unit types (no rule of `Value` produces a term of base type), that
reduction is deterministic, that a term reduces to at most one value, that closed normal forms are
exactly the values, and that multi-step reduction is a congruence in every evaluation position.

## References

* R. Harper, *Practical Foundations for Programming Languages*, 2nd ed., Cambridge University
  Press, 2016: rules (5.4g,h), (8.5a–d), (10.2a–h), (11.2b–h) and (11.6a–e) with the bracketed
  rules and premises of the eager dynamics; Theorems 6.2 and 6.4 (preservation and progress),
  Lemma 6.3 (canonical forms), Theorem 10.1 and Theorem 11.1 (safety for products and sums).
* P. Sewell, *Semantics of Programming Languages*, lecture notes, University of Cambridge
  Computer Science Tripos Part IB, 2025–26: Section 5.1 (products and sums), Section 5.5 and
  Theorems 23–25 (progress, type preservation and type safety).
* B. C. Pierce et al., *Software Foundations*, volume 2, *Programming Language Foundations*,
  chapter `MoreStlc`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.StlcExtended

open scoped CslibStlcExtended

universe u

/-- **Values of the extended simply typed lambda calculus.** A term is a value exactly when it is
a lambda abstraction, the unit value $\langle\rangle$, a pair of values, a left or right injection
of a value, or one of the boolean constants $\mathsf{tt}$ and $\mathsf{ff}$. These are the value
rules of the eager dynamics: rules (8.5a), (10.2a,b), (11.2b,c) and (11.6a,b) of Harper's
*Practical Foundations for Programming Languages*, 2nd ed. None of the rules produces a term of
base type. -/
inductive Value {Base : Type u} : {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → Prop where
  | lam {A B : Ty Base} {Γ : List (Ty Base)} (body : Tm (A :: Γ) B) : Value (.lam body)
  | unit {Γ : List (Ty Base)} : Value (.unit : Tm Γ .unit)
  | pair {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b : Tm Γ B} :
      Value a → Value b → Value (.pair a b)
  | inl {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} :
      Value a → Value (.inl a : Tm Γ (.sum A B))
  | inr {A B : Ty Base} {Γ : List (Ty Base)} {b : Tm Γ B} :
      Value b → Value (.inr b : Tm Γ (.sum A B))
  | tt {Γ : List (Ty Base)} : Value (.tt : Tm Γ .bool)
  | ff {Γ : List (Ty Base)} : Value (.ff : Tm Γ .bool)

/-- **Small-step call-by-value reduction in the extended calculus.** One-step reduction on terms
of type $A$ in a context $\Gamma$ is the least relation closed under the following eager,
left-to-right rules, where $b[a]$ is the result of substituting $a$ for the newest free variable
of $b$:

* functions (rules (8.5b–d)): reduce the function of an application; once it is a value, reduce
  the argument; and $(\lambda b)\,a$ reduces to $b[a]$ when $a$ is a value;
* products (rules (10.2c–h)): reduce the left component of a pair, then the right component once
  the left one is a value; reduce the argument of a projection; and $\mathsf{fst}\,\langle a,
  b\rangle$ and $\mathsf{snd}\,\langle a, b\rangle$ reduce to $a$ and $b$ when $a$ and $b$ are
  values;
* sums (rules (11.2d–h)): reduce the payload of an injection; reduce the scrutinee of a case
  analysis; and $\mathsf{case}\,(\mathsf{inl}\,a)\,l\,r$ reduces to $l[a]$ and
  $\mathsf{case}\,(\mathsf{inr}\,b)\,l\,r$ to $r[b]$ when the payload is a value;
* booleans (rules (11.6c–e)): reduce the condition of a conditional, and
  $\mathsf{ite}\,\mathsf{tt}\,t\,e$ and $\mathsf{ite}\,\mathsf{ff}\,t\,e$ reduce to $t$ and $e$;
* `let` (rules (5.4g,h)): reduce the bound term, and $\mathsf{let}\,a\,b$ reduces to $b[a]$ when
  $a$ is a value.

The rule numbers are those of Harper's *Practical Foundations for Programming Languages*,
2nd ed., with the bracketed rules and premises of the eager dynamics. No rule reduces under a
binder or inside the branches of a conditional or case analysis.

Both sides of every rule are terms of type $A$ in $\Gamma$, so preservation holds by
construction: `Step` is closed under the typing of the calculus because a rule is accepted by
the type checker only when its right-hand side has the type of its left-hand side. The content of
type safety is therefore progress, `Step.progress`, together with this intrinsic closure; the
multi-step corollaries apply progress at every reachable term. -/
inductive Step {Base : Type u} : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm Γ A → Prop where
  | appFun {A B : Ty Base} {Γ : List (Ty Base)} {f f' : Tm Γ (A ⇒ B)} {a : Tm Γ A} :
      Step f f' → Step (.app f a) (.app f' a)
  | appArg {A B : Ty Base} {Γ : List (Ty Base)} {f : Tm Γ (A ⇒ B)} {a a' : Tm Γ A} :
      Value f → Step a a' → Step (.app f a) (.app f a')
  | beta {A B : Ty Base} {Γ : List (Ty Base)} {body : Tm (A :: Γ) B} {a : Tm Γ A} :
      Value a → Step (.app (.lam body) a) (body.instantiate a)
  | pairL {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A} {b : Tm Γ B} :
      Step a a' → Step (.pair a b) (.pair a' b)
  | pairR {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b b' : Tm Γ B} :
      Value a → Step b b' → Step (.pair a b) (.pair a b')
  | fst {A B : Ty Base} {Γ : List (Ty Base)} {p p' : Tm Γ (.prod A B)} :
      Step p p' → Step (.fst p) (.fst p')
  | fstPair {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b : Tm Γ B} :
      Value a → Value b → Step (.fst (.pair a b)) a
  | snd {A B : Ty Base} {Γ : List (Ty Base)} {p p' : Tm Γ (.prod A B)} :
      Step p p' → Step (.snd p) (.snd p')
  | sndPair {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b : Tm Γ B} :
      Value a → Value b → Step (.snd (.pair a b)) b
  | inl {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A} :
      Step a a' → Step (.inl a : Tm Γ (.sum A B)) (.inl a')
  | inr {A B : Ty Base} {Γ : List (Ty Base)} {b b' : Tm Γ B} :
      Step b b' → Step (.inr b : Tm Γ (.sum A B)) (.inr b')
  | case {A B C : Ty Base} {Γ : List (Ty Base)} {s s' : Tm Γ (.sum A B)}
      {l : Tm (A :: Γ) C} {r : Tm (B :: Γ) C} :
      Step s s' → Step (.case s l r) (.case s' l r)
  | caseInl {A B C : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A}
      {l : Tm (A :: Γ) C} {r : Tm (B :: Γ) C} :
      Value a → Step (.case (.inl a) l r) (l.instantiate a)
  | caseInr {A B C : Ty Base} {Γ : List (Ty Base)} {b : Tm Γ B}
      {l : Tm (A :: Γ) C} {r : Tm (B :: Γ) C} :
      Value b → Step (.case (.inr b) l r) (r.instantiate b)
  | ite {A : Ty Base} {Γ : List (Ty Base)} {c c' : Tm Γ .bool} {t e : Tm Γ A} :
      Step c c' → Step (.ite c t e) (.ite c' t e)
  | iteTt {A : Ty Base} {Γ : List (Ty Base)} {t e : Tm Γ A} :
      Step (.ite .tt t e) t
  | iteFf {A : Ty Base} {Γ : List (Ty Base)} {t e : Tm Γ A} :
      Step (.ite .ff t e) e
  | letL {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A} {b : Tm (A :: Γ) B} :
      Step a a' → Step (.letIn a b) (.letIn a' b)
  | letValue {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b : Tm (A :: Γ) B} :
      Value a → Step (.letIn a b) (b.instantiate a)

namespace Value

/-- **A variable is not a value.** -/
theorem not_var {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (x : Var Γ A) :
    ¬ Value (.var x) := by intro h; cases h

/-- **An application is not a value.** -/
theorem not_app {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (f : Tm Γ (A ⇒ B))
    (a : Tm Γ A) : ¬ Value (.app f a) := by intro h; cases h

/-- **A first projection is not a value.** -/
theorem not_fst {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (p : Tm Γ (.prod A B)) :
    ¬ Value (.fst p) := by intro h; cases h

/-- **A second projection is not a value.** -/
theorem not_snd {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (p : Tm Γ (.prod A B)) :
    ¬ Value (.snd p) := by intro h; cases h

/-- **A case analysis is not a value.** -/
theorem not_case {Base : Type u} {A B C : Ty Base} {Γ : List (Ty Base)} (s : Tm Γ (.sum A B))
    (l : Tm (A :: Γ) C) (r : Tm (B :: Γ) C) : ¬ Value (.case s l r) := by intro h; cases h

/-- **A conditional is not a value.** -/
theorem not_ite {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (c : Tm Γ .bool)
    (t e : Tm Γ A) : ¬ Value (.ite c t e) := by intro h; cases h

/-- **A `let` is not a value.** -/
theorem not_letIn {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} (a : Tm Γ A)
    (b : Tm (A :: Γ) B) : ¬ Value (.letIn a b) := by intro h; cases h

end Value

/-- **Canonical forms at function types.** A closed value of type $A \Rightarrow B$ is a lambda
abstraction. -/
theorem closed_value_arr {Base : Type u} {A B : Ty Base} {f : Tm [] (A ⇒ B)} (hv : Value f) :
    ∃ body : Tm [A] B, f = .lam body := by
  cases hv with
  | lam body => exact ⟨body, rfl⟩

/-- **Canonical forms at product types.** A closed value of type $A \times B$ is a pair of
values. -/
theorem closed_value_prod {Base : Type u} {A B : Ty Base} {p : Tm [] (.prod A B)}
    (hv : Value p) : ∃ (a : Tm [] A) (b : Tm [] B), Value a ∧ Value b ∧ p = .pair a b := by
  cases hv with
  | pair ha hb => exact ⟨_, _, ha, hb, rfl⟩

/-- **Canonical forms at sum types.** A closed value of type $A + B$ is a left injection of a
value or a right injection of a value. -/
theorem closed_value_sum {Base : Type u} {A B : Ty Base} {s : Tm [] (.sum A B)} (hv : Value s) :
    (∃ a : Tm [] A, Value a ∧ s = .inl a) ∨ (∃ b : Tm [] B, Value b ∧ s = .inr b) := by
  cases hv with
  | inl ha => exact .inl ⟨_, ha, rfl⟩
  | inr hb => exact .inr ⟨_, hb, rfl⟩

/-- **Canonical forms at the boolean type.** A closed value of type $\mathsf{bool}$ is
$\mathsf{tt}$ or $\mathsf{ff}$. -/
theorem closed_value_bool {Base : Type u} {c : Tm (Base := Base) [] .bool} (hv : Value c) :
    c = .tt ∨ c = .ff := by
  cases hv with
  | tt => exact .inl rfl
  | ff => exact .inr rfl

/-- **Canonical forms at the unit type.** A closed value of type $\mathsf{unit}$ is the unit
value $\langle\rangle$. -/
theorem closed_value_unit {Base : Type u} {u : Tm (Base := Base) [] .unit} (hv : Value u) :
    u = .unit := by cases hv; rfl

namespace Step

/-- **Values are irreducible.** If a term $t$ of type $A$ in a context $\Gamma$ is a value, then
there is no term $t'$ to which $t$ reduces in one step. -/
theorem value_irreducible {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} {t t' : Tm Γ A}
    (hv : Value t) : ¬ Step t t' := by
  induction hv with
  | lam body => intro h; cases h
  | unit => intro h; cases h
  | pair _ _ iha ihb =>
      intro h
      cases h with
      | pairL h => exact iha h
      | pairR _ h => exact ihb h
  | inl _ ih =>
      intro h
      cases h with
      | inl h => exact ih h
  | inr _ ih =>
      intro h
      cases h with
      | inr h => exact ih h
  | tt => intro h; cases h
  | ff => intro h; cases h

/-- **Progress for closed terms.** Every term $t$ of type $A$ in the empty context is either a
value or reduces in one call-by-value step to some term $t'$. Together with preservation, which
holds by construction because `Step` relates terms of the same type, this is the type safety
theorem of the calculus. -/
theorem progress {Base : Type u} : {A : Ty Base} → (t : Tm [] A) → Value t ∨ ∃ t', Step t t' :=
  fun {A} t => match A, t with
    | _, .var x => nomatch x
    | _, .lam body => .inl (.lam body)
    | _, .app f a => by
        rcases progress f with hf | ⟨f', hf'⟩
        · rcases progress a with ha | ⟨a', ha'⟩
          · obtain ⟨body, rfl⟩ := closed_value_arr hf
            exact .inr ⟨_, .beta ha⟩
          · exact .inr ⟨_, .appArg hf ha'⟩
        · exact .inr ⟨_, .appFun hf'⟩
    | _, .unit => .inl .unit
    | _, .pair a b => by
        rcases progress a with ha | ⟨a', ha'⟩
        · rcases progress b with hb | ⟨b', hb'⟩
          · exact .inl (.pair ha hb)
          · exact .inr ⟨_, .pairR ha hb'⟩
        · exact .inr ⟨_, .pairL ha'⟩
    | _, .fst p => by
        rcases progress p with hp | ⟨p', hp'⟩
        · obtain ⟨a, b, ha, hb, rfl⟩ := closed_value_prod hp
          exact .inr ⟨_, .fstPair ha hb⟩
        · exact .inr ⟨_, .fst hp'⟩
    | _, .snd p => by
        rcases progress p with hp | ⟨p', hp'⟩
        · obtain ⟨a, b, ha, hb, rfl⟩ := closed_value_prod hp
          exact .inr ⟨_, .sndPair ha hb⟩
        · exact .inr ⟨_, .snd hp'⟩
    | _, .inl a => by
        rcases progress a with ha | ⟨a', ha'⟩
        · exact .inl (.inl ha)
        · exact .inr ⟨_, .inl ha'⟩
    | _, .inr b => by
        rcases progress b with hb | ⟨b', hb'⟩
        · exact .inl (.inr hb)
        · exact .inr ⟨_, .inr hb'⟩
    | _, .case s l r => by
        rcases progress s with hs | ⟨s', hs'⟩
        · rcases closed_value_sum hs with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
          · exact .inr ⟨_, .caseInl ha⟩
          · exact .inr ⟨_, .caseInr hb⟩
        · exact .inr ⟨_, .case hs'⟩
    | _, .tt => .inl .tt
    | _, .ff => .inl .ff
    | _, .ite c t e => by
        rcases progress c with hc | ⟨c', hc'⟩
        · rcases closed_value_bool hc with rfl | rfl
          · exact .inr ⟨_, .iteTt⟩
          · exact .inr ⟨_, .iteFf⟩
        · exact .inr ⟨_, .ite hc'⟩
    | _, .letIn a b => by
        rcases progress a with ha | ⟨a', ha'⟩
        · exact .inr ⟨_, .letValue ha⟩
        · exact .inr ⟨_, .letL ha'⟩

/-- **Call-by-value reduction is deterministic.** For terms $t$, $t_1$ and $t_2$ of type $A$ in a
context $\Gamma$, if $t$ reduces in one step both to $t_1$ and to $t_2$, then $t_1 = t_2$. -/
theorem deterministic {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} {t t₁ t₂ : Tm Γ A}
    (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ := by
  induction h₁ with
  | appFun h ih =>
      cases h₂ with
      | appFun h' => rw [ih h']
      | appArg hv _ => exact absurd h (value_irreducible hv)
      | beta _ => cases h
  | appArg hv h ih =>
      cases h₂ with
      | appFun h' => exact absurd h' (value_irreducible hv)
      | appArg _ h' => rw [ih h']
      | beta hva => exact absurd h (value_irreducible hva)
  | beta hva =>
      cases h₂ with
      | appFun h' => cases h'
      | appArg _ h' => exact absurd h' (value_irreducible hva)
      | beta _ => rfl
  | pairL h ih =>
      cases h₂ with
      | pairL h' => rw [ih h']
      | pairR hva _ => exact absurd h (value_irreducible hva)
  | pairR hva h ih =>
      cases h₂ with
      | pairL h' => exact absurd h' (value_irreducible hva)
      | pairR _ h' => rw [ih h']
  | fst h ih =>
      cases h₂ with
      | fst h' => rw [ih h']
      | fstPair ha hb => exact absurd h (value_irreducible (.pair ha hb))
  | fstPair ha hb =>
      cases h₂ with
      | fst h' => exact absurd h' (value_irreducible (.pair ha hb))
      | fstPair _ _ => rfl
  | snd h ih =>
      cases h₂ with
      | snd h' => rw [ih h']
      | sndPair ha hb => exact absurd h (value_irreducible (.pair ha hb))
  | sndPair ha hb =>
      cases h₂ with
      | snd h' => exact absurd h' (value_irreducible (.pair ha hb))
      | sndPair _ _ => rfl
  | inl h ih =>
      cases h₂ with
      | inl h' => rw [ih h']
  | inr h ih =>
      cases h₂ with
      | inr h' => rw [ih h']
  | case h ih =>
      cases h₂ with
      | case h' => rw [ih h']
      | caseInl hv => exact absurd h (value_irreducible (.inl hv))
      | caseInr hv => exact absurd h (value_irreducible (.inr hv))
  | caseInl hv =>
      cases h₂ with
      | case h' => exact absurd h' (value_irreducible (.inl hv))
      | caseInl _ => rfl
  | caseInr hv =>
      cases h₂ with
      | case h' => exact absurd h' (value_irreducible (.inr hv))
      | caseInr _ => rfl
  | ite h ih =>
      cases h₂ with
      | ite h' => rw [ih h']
      | iteTt => cases h
      | iteFf => cases h
  | iteTt =>
      cases h₂ with
      | ite h' => cases h'
      | iteTt => rfl
  | iteFf =>
      cases h₂ with
      | ite h' => cases h'
      | iteFf => rfl
  | letL h ih =>
      cases h₂ with
      | letL h' => rw [ih h']
      | letValue hv => exact absurd h (value_irreducible hv)
  | letValue hv =>
      cases h₂ with
      | letL h' => exact absurd h' (value_irreducible hv)
      | letValue _ => rfl

/-- **Normal forms for call-by-value reduction.** A term $t$ of type $A$ in a context $\Gamma$ is
in normal form when there is no term $t'$ such that $t$ reduces to $t'$ in one step.

This is `Relation.Normal Step` (see `normalForm_iff_normal`). Since `Step` never reduces under a
binder, every abstraction is a normal form here, even one whose body contains a redex. -/
def NormalForm {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} (t : Tm Γ A) : Prop :=
  ∀ t', ¬ Step t t'

/-- **Normal forms are the normal forms of the step relation.** `NormalForm` is the predicate
`Relation.Normal` for `Step`. -/
theorem normalForm_iff_normal {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} {t : Tm Γ A} :
    NormalForm t ↔ Relation.Normal Step t := not_exists.symm

/-- **Closed normal forms are exactly the values.** A term $t$ of type $A$ in the empty context is
in normal form if and only if it is a value. -/
theorem closed_normalForm_iff_value {Base : Type u} {A : Ty Base} (t : Tm [] A) :
    NormalForm t ↔ Value t := by
  constructor
  · intro hnormal
    rcases progress t with hv | ⟨t', hstep⟩
    · exact hv
    · exact (hnormal t' hstep).elim
  · intro hv t' hstep
    exact value_irreducible hv hstep

end Step

/-- **Multi-step call-by-value reduction.** For terms of type $A$ in a context $\Gamma$,
multi-step reduction is the reflexive transitive closure of one-step reduction. -/
abbrev Steps {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :=
  Relation.ReflTransGen (@Step Base Γ A)

namespace Steps

/-- **A term reduces to at most one value.** If $t$ reduces in any number of steps to values
$v_1$ and $v_2$, then $v_1 = v_2$. -/
theorem value_unique {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} {t v₁ v₂ : Tm Γ A}
    (h₁ : Steps t v₁) (h₂ : Steps t v₂) (hv₁ : Value v₁) (hv₂ : Value v₂) : v₁ = v₂ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨c, hc, _⟩
      · rfl
      · exact absurd hc (Step.value_irreducible hv₁)
  | head hs _ ih =>
      rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨c, hc, hrest⟩
      · exact absurd hs (Step.value_irreducible hv₂)
      · obtain rfl := Step.deterministic hs hc
        exact ih hrest

/-- **Multi-step reduction in the function of an application.** -/
theorem appFun {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {f f' : Tm Γ (A ⇒ B)}
    {a : Tm Γ A} (h : Steps f f') : Steps (.app f a) (.app f' a) := by
  exact Relation.ReflTransGen.lift (fun f => Tm.app f a) (fun _ _ h => Step.appFun h) _ _ h

/-- **Multi-step reduction in the argument of an application whose function is a value.** -/
theorem appArg {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {f : Tm Γ (A ⇒ B)}
    {a a' : Tm Γ A} (hf : Value f) (h : Steps a a') : Steps (.app f a) (.app f a') := by
  exact Relation.ReflTransGen.lift (Tm.app f) (fun _ _ h => Step.appArg hf h) _ _ h

/-- **Multi-step reduction in the left component of a pair.** -/
theorem pairL {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A} {b : Tm Γ B}
    (h : Steps a a') : Steps (.pair a b) (.pair a' b) := by
  exact Relation.ReflTransGen.lift (fun a => Tm.pair a b) (fun _ _ h => Step.pairL h) _ _ h

/-- **Multi-step reduction in the right component of a pair whose left component is a
value.** -/
theorem pairR {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {a : Tm Γ A} {b b' : Tm Γ B}
    (ha : Value a) (h : Steps b b') : Steps (.pair a b) (.pair a b') := by
  exact Relation.ReflTransGen.lift (Tm.pair a) (fun _ _ h => Step.pairR ha h) _ _ h

/-- **Multi-step reduction in the argument of a first projection.** -/
theorem fst {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {p p' : Tm Γ (.prod A B)}
    (h : Steps p p') : Steps (.fst p) (.fst p') := by
  exact Relation.ReflTransGen.lift Tm.fst (fun _ _ h => Step.fst h) _ _ h

/-- **Multi-step reduction in the argument of a second projection.** -/
theorem snd {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {p p' : Tm Γ (.prod A B)}
    (h : Steps p p') : Steps (.snd p) (.snd p') := by
  exact Relation.ReflTransGen.lift Tm.snd (fun _ _ h => Step.snd h) _ _ h

/-- **Multi-step reduction in the payload of a left injection.** -/
theorem inl {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A}
    (h : Steps a a') : Steps (.inl a : Tm Γ (.sum A B)) (.inl a') := by
  exact Relation.ReflTransGen.lift (fun a => (Tm.inl a : Tm Γ (.sum A B)))
    (fun _ _ h => Step.inl h) _ _ h

/-- **Multi-step reduction in the payload of a right injection.** -/
theorem inr {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {b b' : Tm Γ B}
    (h : Steps b b') : Steps (.inr b : Tm Γ (.sum A B)) (.inr b') := by
  exact Relation.ReflTransGen.lift (fun b => (Tm.inr b : Tm Γ (.sum A B)))
    (fun _ _ h => Step.inr h) _ _ h

/-- **Multi-step reduction in the scrutinee of a case analysis.** -/
theorem case {Base : Type u} {A B C : Ty Base} {Γ : List (Ty Base)} {s s' : Tm Γ (.sum A B)}
    {l : Tm (A :: Γ) C} {r : Tm (B :: Γ) C} (h : Steps s s') :
    Steps (.case s l r) (.case s' l r) := by
  exact Relation.ReflTransGen.lift (fun s => Tm.case s l r) (fun _ _ h => Step.case h) _ _ h

/-- **Multi-step reduction in the condition of a conditional.** -/
theorem ite {Base : Type u} {A : Ty Base} {Γ : List (Ty Base)} {c c' : Tm Γ .bool}
    {t e : Tm Γ A} (h : Steps c c') : Steps (.ite c t e) (.ite c' t e) := by
  exact Relation.ReflTransGen.lift (fun c => Tm.ite c t e) (fun _ _ h => Step.ite h) _ _ h

/-- **Multi-step reduction in the bound term of a `let`.** -/
theorem letL {Base : Type u} {A B : Ty Base} {Γ : List (Ty Base)} {a a' : Tm Γ A}
    {b : Tm (A :: Γ) B} (h : Steps a a') : Steps (.letIn a b) (.letIn a' b) := by
  exact Relation.ReflTransGen.lift (fun a => Tm.letIn a b) (fun _ _ h => Step.letL h) _ _ h

end Steps

end Cslib.Languages.LambdaCalculus.StlcExtended
