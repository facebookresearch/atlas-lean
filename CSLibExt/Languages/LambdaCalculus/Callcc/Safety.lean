/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.Callcc.Basic
public import CSLibExt.Languages.TypeSafety
public import Cslib.Foundations.Relation.Defs
import Cslib.Foundations.Relation.Preserves

/-!
# First-class continuations with callcc and abort: type safety

Structural properties of the typing judgment of
`CSLibExt.Languages.LambdaCalculus.Callcc.Basic` (renaming, weakening, substitution and
instantiation), the lemmas on evaluation contexts (renaming commutes with plugging, typing of a
plugged context and of the continuation of a context), progress for closed terms at every type,
and preservation for closed programs at their answer type, which is the form of subject
reduction that holds for program reductions (Wright and Felleisen, Main Lemma 6.5). With the
type-safety schema of `CSLibExt.Languages.TypeSafety`, taking a closed program as the state and
values as the final states, these give the multi-step safety statements, and the typing
judgment satisfies the structural-typing interface. `callcc` has the type of Peirce's law, and
the answer type is irrelevant for abort-free terms, which gives safety for abort-free programs at
every type, with every term they reach, in particular the value they reach, typed at the type of
the program (Wright and Felleisen, Theorem 6.6).

## References

* A. K. Wright and M. Felleisen, *A Syntactic Approach to Type Soundness*, Information and
  Computation 115(1), 1994, §6: the claim in the proof of Main Lemma 6.1 (typing of the
  continuation), §6.4, Lemma 6.4, Main Lemma 6.5 and Theorem 6.6, with a single answer type.
* T. G. Griffin, *A Formulae-as-Types Notion of Control*, POPL 1990, §5: callcc has the type of
  Peirce's law.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.Callcc

/-! ### Structural properties of typing -/

/-- **Renaming preserves typing.** Let `T` be the answer type, `Γ` and `Δ` contexts, and `ρ` a
renaming of de Bruijn indices such that whenever `Γ` assigns the type `B` to the variable `x`,
the context `Δ` assigns `B` to `ρ x`. If `e` has type `A` in `Γ`, then `e.rename ρ` has type `A`
in `Δ`. -/
theorem HasType.rename {T : Ty} {Γ Δ : List Ty} {e : Term} {A : Ty} (h : HasType T Γ e A)
    {ρ : ℕ → ℕ} (hρ : ∀ x B, Γ[x]? = some B → Δ[ρ x]? = some B) :
    HasType T Δ (e.rename ρ) A := by
  induction h generalizing Δ ρ with
  | var hx => exact .var (hρ _ _ hx)
  | lam _ ih =>
    refine .lam (ih ?_)
    intro x B hx
    cases x with
    | zero => exact hx
    | succ x => exact hρ x B hx
  | app _ _ ihf iha => exact .app (ihf hρ) (iha hρ)
  | num => exact .num
  | mul _ _ iha ihb => exact .mul (iha hρ) (ihb hρ)
  | ifz _ _ _ ihc iht ihe => exact .ifz (ihc hρ) (iht hρ) (ihe hρ)
  | callcc _ ih => exact .callcc (ih hρ)
  | abort _ ih => exact .abort (ih hρ)

/-- **Weakening.** Let `T` be the answer type. If `e` has type `A` in the context `Γ`, then for
every type `B`, the term `e` with every free variable raised by one has type `A` in `Γ` extended
by a new innermost variable of type `B`. -/
theorem HasType.weaken {T : Ty} {Γ : List Ty} {e : Term} {A : Ty} (B : Ty)
    (h : HasType T Γ e A) : HasType T (B :: Γ) (e.rename (· + 1)) A := by
  exact h.rename fun _ _ hx => hx

/-- **Parallel substitution preserves typing.** Let `T` be the answer type, `Γ` and `Δ`
contexts, and `σ` a substitution such that whenever `Γ` assigns the type `B` to the variable
`x`, the term `σ x` has type `B` in `Δ`. If `e` has type `A` in `Γ`, then `e.subst σ` has type
`A` in `Δ`. -/
theorem HasType.subst {T : Ty} {Γ Δ : List Ty} {e : Term} {A : Ty} (h : HasType T Γ e A)
    {σ : ℕ → Term} (hσ : ∀ x B, Γ[x]? = some B → HasType T Δ (σ x) B) :
    HasType T Δ (e.subst σ) A := by
  induction h generalizing Δ σ with
  | var hx => exact hσ _ _ hx
  | lam _ ih =>
    refine .lam (ih ?_)
    intro x B hx
    cases x with
    | zero => exact .var hx
    | succ x => exact (hσ x B hx).weaken _
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | num => exact .num
  | mul _ _ iha ihb => exact .mul (iha hσ) (ihb hσ)
  | ifz _ _ _ ihc iht ihe => exact .ifz (ihc hσ) (iht hσ) (ihe hσ)
  | callcc _ ih => exact .callcc (ih hσ)
  | abort _ ih => exact .abort (ih hσ)

/-- **Substitution lemma.** Let `T` be the answer type. If `b` has type `B` in the context `Γ`
extended by a new innermost variable of type `A`, and `s` has type `A` in `Γ`, then
`b.instantiate s` has type `B` in `Γ`. -/
theorem HasType.instantiate {T : Ty} {Γ : List Ty} {b s : Term} {A B : Ty}
    (hb : HasType T (A :: Γ) b B) (hs : HasType T Γ s A) :
    HasType T Γ (b.instantiate s) B := by
  refine hb.subst ?_
  intro x C hx
  cases x with
  | zero =>
    cases hx
    exact hs
  | succ x => exact .var hx

/-! ### Evaluation contexts -/

/-- **Renaming commutes with plugging.** For every evaluation context `E`, renaming `ρ` and term
`t`, plugging the renamed term into the renamed context gives the renaming of the plugged
term. -/
theorem ECtx.rename_plug (E : ECtx) (ρ : ℕ → ℕ) (t : Term) :
    (E.rename ρ).plug (t.rename ρ) = (E.plug t).rename ρ := by
  induction E generalizing t with
  | nil => rfl
  | cons F E ih =>
    cases F with
    | appL a => exact ih (.app t a)
    | appR f => exact ih (.app f t)
    | mulL b => exact ih (.mul t b)
    | mulR a => exact ih (.mul a t)
    | ifz t₁ t₂ => exact ih (.ifz t t₁ t₂)
    | callcc => exact ih (.callcc t)

/-- **Typing of a plugged context, inverted.** Let `T` be the answer type and `Γ` a context. If
`E.plug e` has type `B` in `Γ`, then for some type `A`, the term `e` has type `A` in `Γ` and the
context `E` has type `A` to `B` in `Γ`. -/
theorem HasType.plug_inv {T : Ty} {Γ : List Ty} {E : ECtx} {e : Term} {B : Ty}
    (h : HasType T Γ (E.plug e) B) : ∃ A, HasType T Γ e A ∧ HasCtxType T Γ E A B := by
  induction E generalizing e with
  | nil => exact ⟨B, h, .nil⟩
  | cons F E ih =>
    cases F with
    | appL a =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | app hf ha => exact ⟨_, hf, .appL ha hE⟩
    | appR f =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | app hf ha => exact ⟨_, ha, .appR hf hE⟩
    | mulL b =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | mul ha hb => exact ⟨_, ha, .mulL hb hE⟩
    | mulR a =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | mul ha hb => exact ⟨_, hb, .mulR ha hE⟩
    | ifz t₁ t₂ =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | ifz hc ht he => exact ⟨_, hc, .ifz ht he hE⟩
    | callcc =>
      obtain ⟨C, hC, hE⟩ := ih h
      cases hC with
      | callcc h' => exact ⟨_, h', .callcc hE⟩

/-- **Typing of a plugged context.** Let `T` be the answer type and `Γ` a context. If the context
`E` has type `A` to `B` in `Γ` and `e` has type `A` in `Γ`, then `E.plug e` has type `B` in
`Γ`. -/
theorem HasType.plug {T : Ty} {Γ : List Ty} {E : ECtx} {e : Term} {A B : Ty}
    (hE : HasCtxType T Γ E A B) (he : HasType T Γ e A) : HasType T Γ (E.plug e) B := by
  induction hE generalizing e with
  | nil => exact he
  | appL ha _ ih => exact ih (.app he ha)
  | appR hf _ ih => exact ih (.app hf he)
  | mulL hb _ ih => exact ih (.mul he hb)
  | mulR ha _ ih => exact ih (.mul ha he)
  | ifz ht he' _ ih => exact ih (.ifz he ht he')
  | callcc _ ih => exact ih (.callcc he)

/-- **Renaming preserves the typing of contexts.** Let `T` be the answer type, `Γ` and `Δ`
contexts, and `ρ` a renaming of de Bruijn indices such that whenever `Γ` assigns the type `C` to
the variable `x`, the context `Δ` assigns `C` to `ρ x`. If `E` has type `A` to `B` in `Γ`, then
`E.rename ρ` has type `A` to `B` in `Δ`. -/
theorem HasCtxType.rename {T : Ty} {Γ Δ : List Ty} {E : ECtx} {A B : Ty}
    (h : HasCtxType T Γ E A B) {ρ : ℕ → ℕ} (hρ : ∀ x C, Γ[x]? = some C → Δ[ρ x]? = some C) :
    HasCtxType T Δ (E.rename ρ) A B := by
  induction h with
  | nil => exact .nil
  | appL ha _ ih => exact .appL (ha.rename hρ) ih
  | appR hf _ ih => exact .appR (hf.rename hρ) ih
  | mulL hb _ ih => exact .mulL (hb.rename hρ) ih
  | mulR ha _ ih => exact .mulR (ha.rename hρ) ih
  | ifz ht he _ ih => exact .ifz (ht.rename hρ) (he.rename hρ) ih
  | callcc _ ih => exact .callcc ih

/-- **Typing of the continuation of a context.** Let `T` be the answer type and `Γ` a context.
If the context `E` has type `A` to `T` in `Γ`, then for every type `B` its continuation
`λx. abort E[x]` has type `A → B` in `Γ`. -/
theorem HasType.reify {T : Ty} {Γ : List Ty} {E : ECtx} {A B : Ty}
    (h : HasCtxType T Γ E A T) : HasType T Γ E.reify (.arr A B) := by
  exact .lam (.abort (HasType.plug (h.rename (Δ := A :: Γ) fun _ _ hx => hx) (.var rfl)))

/-! ### Progress and preservation -/

/-- A value of a function type is an abstraction. -/
private theorem canonical_arr {T : Ty} {Γ : List Ty} {v : Term} {A B : Ty} (hv : v.Value)
    (h : HasType T Γ v (.arr A B)) : ∃ b, v = .lam b := by
  cases hv with
  | lam b => exact ⟨b, rfl⟩
  | num n => cases h

/-- A value of type `nat` is a numeral. -/
private theorem canonical_nat {T : Ty} {Γ : List Ty} {v : Term} (hv : v.Value)
    (h : HasType T Γ v .nat) : ∃ n, v = .num n := by
  cases hv with
  | lam b => cases h
  | num n => exact ⟨n, rfl⟩

/-- Plugging a concatenation of contexts plugs the inner context first. -/
private theorem ECtx.plug_append (E₁ E₂ : ECtx) (t : Term) :
    ECtx.plug (E₁ ++ E₂) t = E₂.plug (E₁.plug t) := by
  induction E₁ generalizing t with
  | nil => rfl
  | cons F E ih => cases F <;> exact ih _

/-- A concatenation of admissible contexts is admissible. -/
private theorem ECtx.Ok.append {E₁ E₂ : ECtx} (h₁ : E₁.Ok) (h₂ : E₂.Ok) :
    ECtx.Ok (E₁ ++ E₂) := by
  induction E₁ with
  | nil => exact h₂
  | cons F E ih =>
    cases F with
    | appL a => exact ih h₁
    | appR f => exact ⟨h₁.1, ih h₁.2⟩
    | mulL b => exact ih h₁
    | mulR a => exact ⟨h₁.1, ih h₁.2⟩
    | ifz t e => exact ih h₁
    | callcc => exact ih h₁

/-- A term that steps still steps inside an admissible context. -/
private theorem Step.extend {e e' : Term} (hs : Step e e') (E' : ECtx) (hE' : E'.Ok) :
    ∃ e'', Step (E'.plug e) e'' := by
  cases hs with
  | red hE hr =>
    rw [← ECtx.plug_append]
    exact ⟨_, Step.red (ECtx.Ok.append hE hE') hr⟩
  | callcc hE hv =>
    rw [← ECtx.plug_append]
    exact ⟨_, Step.callcc (ECtx.Ok.append hE hE') hv⟩
  | abort hE =>
    rw [← ECtx.plug_append]
    exact ⟨_, Step.abort (ECtx.Ok.append hE hE')⟩

/-- **Progress.** Let `T` be the answer type. A closed term of type `A` is a value or takes a
step. -/
theorem progress {T : Ty} {e : Term} {A : Ty} (h : HasType T [] e A) :
    e.Value ∨ ∃ e', Step e e' := by
  generalize hΓ : ([] : List Ty) = Γ at h
  induction h with
  | var hx =>
    subst hΓ
    simp at hx
  | lam _ _ => exact .inl (.lam _)
  | num => exact .inl (.num _)
  | app hf _ ihf iha =>
    rcases ihf hΓ with hvf | ⟨f', hf'⟩
    · rcases iha hΓ with hva | ⟨a', ha'⟩
      · obtain ⟨b, rfl⟩ := canonical_arr hvf hf
        exact .inr ⟨_, Step.red (E := []) trivial (.beta hva)⟩
      · exact .inr (Step.extend ha' [.appR _] ⟨hvf, trivial⟩)
    · exact .inr (Step.extend hf' [.appL _] trivial)
  | mul ha hb iha ihb =>
    rcases iha hΓ with hva | ⟨a', ha'⟩
    · rcases ihb hΓ with hvb | ⟨b', hb'⟩
      · obtain ⟨m, rfl⟩ := canonical_nat hva ha
        obtain ⟨n, rfl⟩ := canonical_nat hvb hb
        exact .inr ⟨_, Step.red (E := []) trivial .mul⟩
      · exact .inr (Step.extend hb' [.mulR _] ⟨hva, trivial⟩)
    · exact .inr (Step.extend ha' [.mulL _] trivial)
  | ifz hc _ _ ihc _ _ =>
    rcases ihc hΓ with hvc | ⟨c', hc'⟩
    · obtain ⟨n, rfl⟩ := canonical_nat hvc hc
      cases n with
      | zero => exact .inr ⟨_, Step.red (E := []) trivial .ifzZero⟩
      | succ n => exact .inr ⟨_, Step.red (E := []) trivial .ifzSucc⟩
    · exact .inr (Step.extend hc' [.ifz _ _] trivial)
  | callcc _ ih =>
    rcases ih hΓ with hv | ⟨e', he'⟩
    · exact .inr ⟨_, Step.callcc (E := []) trivial hv⟩
    · exact .inr (Step.extend he' [.callcc] trivial)
  | abort _ _ => exact .inr ⟨_, Step.abort (E := []) trivial⟩

/-- Local reductions preserve typing. -/
private theorem Red.preserves {T : Ty} {Γ : List Ty} {r r' : Term} {A : Ty}
    (h : HasType T Γ r A) (hr : Red r r') : HasType T Γ r' A := by
  cases hr with
  | beta _ =>
    cases h with
    | app hf ha =>
      cases hf with
      | lam hb => exact hb.instantiate ha
  | mul =>
    cases h
    exact .num
  | ifzZero =>
    cases h with
    | ifz _ ht _ => exact ht
  | ifzSucc =>
    cases h with
    | ifz _ _ he => exact he

/-- **Preservation for programs.** Let `T` be the answer type. If a closed program `e` has type
`T` and `e` steps to `e'`, then `e'` has type `T`. -/
theorem preservation {T : Ty} {e e' : Term} (h : HasType T [] e T) (hs : Step e e') :
    HasType T [] e' T := by
  cases hs with
  | red _ hr =>
    obtain ⟨A, hA, hE⟩ := HasType.plug_inv h
    exact HasType.plug hE (Red.preserves hA hr)
  | callcc _ _ =>
    obtain ⟨A, hA, hE⟩ := HasType.plug_inv h
    cases hA with
    | callcc hv => exact HasType.plug hE (.app hv (HasType.reify hE))
  | abort _ =>
    obtain ⟨A, hA, _⟩ := HasType.plug_inv h
    cases hA with
    | abort he => exact he

/-! ### Safety through the schema -/

/-- **Typed programs reach only values or reducible programs.** Let `T` be the answer type.
Every term reachable in any number of steps from a closed program of type `T` is a value or
takes a step. -/
theorem final_or_step {T : Ty} {e e' : Term} (h : HasType T [] e T)
    (hr : Relation.ReflTransGen Step e e') : e'.Value ∨ ∃ e'', Step e' e'' := by
  exact TypeSafety.final_or_step_of_reflTransGen Step Term.Value
    (fun e T => HasType T [] e T) (fun he => progress he)
    (fun _ _ _ hs he => preservation he hs) h hr

/-- **Typed programs never get stuck.** Let `T` be the answer type. No term reachable in any
number of steps from a closed program of type `T` is a normal form that is not a value. -/
theorem not_stuck {T : Ty} {e e' : Term} (h : HasType T [] e T)
    (hr : Relation.ReflTransGen Step e e') : ¬ (¬ e'.Value ∧ Relation.Normal Step e') := by
  exact TypeSafety.not_stuck_of_reflTransGen Step Term.Value
    (fun e T => HasType T [] e T) (fun he => progress he)
    (fun _ _ _ hs he => preservation he hs) h hr

/-- **The calculus with callcc has the structural properties.** For every answer type `T`, the
typing judgment satisfies `TypeSafety.StructuralTyping` when binding adds a new innermost
variable, instantiation is `Term.instantiate`, a context `Γ` extends to `Θ ++ Γ` for every block
`Θ` of new innermost variables, and weakening raises every free variable by the difference of
the context lengths. -/
theorem structuralTyping (T : Ty) :
    TypeSafety.StructuralTyping (HasType T) (fun Γ (_ : Unit) A => A :: Γ)
      (fun t (_ : Unit) s => t.instantiate s) (fun Γ Δ => ∃ Θ, Δ = Θ ++ Γ)
      (fun Γ Δ t => t.rename (· + (Δ.length - Γ.length))) := by
  refine ⟨fun hbody hs => HasType.instantiate hbody hs, ?_⟩
  rintro Γ Δ t A ⟨Θ, rfl⟩ ht
  refine ht.rename fun x B hx => ?_
  rw [List.length_append, Nat.add_sub_cancel,
    List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
  exact hx

/-! ### Peirce's law and abort-free programs -/

/-- **Callcc has the type of Peirce's law.** For every answer type `T`, context `Γ` and types
`A` and `B`, the term `λf. callcc f` has type `((A → B) → A) → A` in `Γ`. -/
theorem peirce {T : Ty} {Γ : List Ty} {A B : Ty} :
    HasType T Γ (.lam (.callcc (.var 0))) (.arr (.arr (.arr A B) A) A) := by
  exact .lam (.callcc (.var rfl))

/-- **The answer type is irrelevant without abort.** If an abort-free term `e` has type `A` in
the context `Γ` at answer type `T`, then it has type `A` in `Γ` at every answer type `T'`. -/
theorem HasType.answer_irrelevant {T T' : Ty} {Γ : List Ty} {e : Term} {A : Ty}
    (he : e.AbortFree) (h : HasType T Γ e A) : HasType T' Γ e A := by
  induction h with
  | var hx => exact .var hx
  | lam _ ih => exact .lam (ih he)
  | app _ _ ihf iha => exact .app (ihf he.1) (iha he.2)
  | num => exact .num
  | mul _ _ iha ihb => exact .mul (iha he.1) (ihb he.2)
  | ifz _ _ _ ihc iht ihe => exact .ifz (ihc he.1) (iht he.2.1) (ihe he.2.2)
  | callcc _ ih => exact .callcc (ih he)
  | abort _ _ => exact (he : False).elim

/-- **Abort-free programs never get stuck.** Let `T` be the answer type. Every term reachable in
any number of steps from an abort-free closed term of type `A` is a value or takes a step. -/
theorem final_or_step_abortFree {T : Ty} {e e' : Term} {A : Ty} (he : e.AbortFree)
    (h : HasType T [] e A) (hr : Relation.ReflTransGen Step e e') :
    e'.Value ∨ ∃ e'', Step e' e'' := by
  exact final_or_step (T := A) (HasType.answer_irrelevant he h) hr

/-- **Syntactic soundness for abort-free programs.** Let `T` be the answer type. Every term
reachable in any number of steps from an abort-free closed term `e` of type `A` has type `A` at
answer type `A`, and is a value or takes a step; in particular a value reached from `e` has type
`A`. The reached terms are typed at answer type `A`, the type of the program, rather than at `T`,
since the continuation that a `callcc` step passes aborts with a term of type `A`. This is Wright
and Felleisen's Theorem 6.6 for every reachable term, with the answer typed as in its proof. -/
theorem hasType_and_final_or_step_abortFree {T : Ty} {e e' : Term} {A : Ty} (he : e.AbortFree)
    (h : HasType T [] e A) (hr : Relation.ReflTransGen Step e e') :
    HasType A [] e' A ∧ (e'.Value ∨ ∃ e'', Step e' e'') := by
  have hp : Relation.Preserves Step (HasType A [] · A) := fun _ _ hs he' => preservation he' hs
  exact ⟨Relation.preserves_reflTransGen_iff.mpr hp hr (HasType.answer_irrelevant he h),
    final_or_step_abortFree he h hr⟩

end Cslib.Languages.LambdaCalculus.Callcc
