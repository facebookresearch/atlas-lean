/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.Exceptions.Basic
public import CSLibExt.Languages.TypeSafety
public import Cslib.Foundations.Relation.Defs
import Cslib.Foundations.Relation.Preserves

/-!
# Exceptions with a fixed exception type: type safety

Structural properties of the typing judgment of
`CSLibExt.Languages.LambdaCalculus.Exceptions.Basic` (renaming, weakening, substitution and
instantiation), the fact that final terms do not step, progress for closed terms (a closed
well-typed term is final, that is a value or an uncaught exception, or it steps), and
preservation for every context. With the type-safety schema of
`CSLibExt.Languages.TypeSafety`, taking a closed term as the state, these give the multi-step
safety statements, and with preservation every term reached from a closed term of type `A`, in
particular a final one, has type `A` (syntactic soundness). The typing judgment satisfies the
structural-typing interface.

## References

* R. Harper, *Practical Foundations for Programming Languages*, 2nd ed., chapter "Exceptions",
  Theorem 29.2 (safety) and final states (29.6).
* A. K. Wright and M. Felleisen, *A Syntactic Approach to Type Soundness*, Information and
  Computation 115(1), 1994, §5.2: Main Lemma 5.8 (subject reduction) and Theorem 5.10
  (syntactic soundness), specialized to one anonymous exception.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.LambdaCalculus.Exceptions

/-! ### Structural properties of typing -/

/-- **Renaming preserves typing.** Let `exn` be the exception type, `Γ` and `Δ` contexts, and
`ρ` a renaming of de Bruijn indices such that whenever `Γ` assigns the type `B` to the variable
`x`, the context `Δ` assigns `B` to `ρ x`. If `e` has type `A` in `Γ`, then `e.rename ρ` has
type `A` in `Δ`. -/
theorem HasType.rename {exn : Ty} {Γ Δ : List Ty} {e : Term} {A : Ty} (h : HasType exn Γ e A)
    {ρ : ℕ → ℕ} (hρ : ∀ x B, Γ[x]? = some B → Δ[ρ x]? = some B) :
    HasType exn Δ (e.rename ρ) A := by
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
  | raise _ ih => exact .raise (ih hρ)
  | tryWith _ _ ih₁ ih₂ =>
    refine .tryWith (ih₁ hρ) (ih₂ ?_)
    intro x B hx
    cases x with
    | zero => exact hx
    | succ x => exact hρ x B hx

/-- **Weakening.** Let `exn` be the exception type. If `e` has type `A` in the context `Γ`, then
for every type `B`, the term `e` with every free variable raised by one has type `A` in `Γ`
extended by a new innermost variable of type `B`. -/
theorem HasType.weaken {exn : Ty} {Γ : List Ty} {e : Term} {A : Ty} (B : Ty)
    (h : HasType exn Γ e A) : HasType exn (B :: Γ) (e.rename (· + 1)) A := by
  exact h.rename fun _ _ hx => hx

/-- **Parallel substitution preserves typing.** Let `exn` be the exception type, `Γ` and `Δ`
contexts, and `σ` a substitution such that whenever `Γ` assigns the type `B` to the variable
`x`, the term `σ x` has type `B` in `Δ`. If `e` has type `A` in `Γ`, then `e.subst σ` has type
`A` in `Δ`. -/
theorem HasType.subst {exn : Ty} {Γ Δ : List Ty} {e : Term} {A : Ty} (h : HasType exn Γ e A)
    {σ : ℕ → Term} (hσ : ∀ x B, Γ[x]? = some B → HasType exn Δ (σ x) B) :
    HasType exn Δ (e.subst σ) A := by
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
  | raise _ ih => exact .raise (ih hσ)
  | tryWith _ _ ih₁ ih₂ =>
    refine .tryWith (ih₁ hσ) (ih₂ ?_)
    intro x B hx
    cases x with
    | zero => exact .var hx
    | succ x => exact (hσ x B hx).weaken _

/-- **Substitution lemma.** Let `exn` be the exception type. If `b` has type `B` in the context
`Γ` extended by a new innermost variable of type `A`, and `s` has type `A` in `Γ`, then
`b.instantiate s` has type `B` in `Γ`. -/
theorem HasType.instantiate {exn : Ty} {Γ : List Ty} {b s : Term} {A B : Ty}
    (hb : HasType exn (A :: Γ) b B) (hs : HasType exn Γ s A) :
    HasType exn Γ (b.instantiate s) B := by
  refine hb.subst ?_
  intro x C hx
  cases x with
  | zero =>
    cases hx
    exact hs
  | succ x => exact .var hx

/-! ### Progress and preservation -/

/-- A term that steps is not a value. -/
private theorem Step.not_value {e e' : Term} (h : Step e e') : ¬ e.Value := by
  intro hv
  cases h with
  | beta => cases hv
  | mul => cases hv
  | ifzZero => cases hv
  | ifzSucc => cases hv
  | @propagate F _ _ _ _ => cases F <;> cases hv
  | tryValue => cases hv
  | tryRaise => cases hv
  | @frame F _ _ _ _ => cases F <;> cases hv

/-- A value of a function type is an abstraction. -/
private theorem canonical_arr {exn : Ty} {Γ : List Ty} {v : Term} {A B : Ty} (hv : v.Value)
    (h : HasType exn Γ v (.arr A B)) : ∃ b, v = .lam b := by
  cases hv with
  | lam b => exact ⟨b, rfl⟩
  | num n => cases h

/-- A value of type `nat` is a numeral. -/
private theorem canonical_nat {exn : Ty} {Γ : List Ty} {v : Term} (hv : v.Value)
    (h : HasType exn Γ v .nat) : ∃ n, v = .num n := by
  cases hv with
  | lam b => cases h
  | num n => exact ⟨n, rfl⟩

/-- **Final terms do not step.** A value, or an uncaught exception `raise v` with `v` a value,
has no step. -/
theorem Final.normal {e : Term} (h : Final e) : Relation.Normal Step e := by
  rintro ⟨e', hs⟩
  rcases h with hv | ⟨v, hv, rfl⟩
  · exact Step.not_value hs hv
  · generalize ht : Term.raise v = t at hs
    cases hs with
    | beta => cases ht
    | mul => cases ht
    | ifzZero => cases ht
    | ifzSucc => cases ht
    | @propagate F w _ _ _ =>
      cases F <;> cases ht
      cases hv
    | tryValue => cases ht
    | tryRaise => cases ht
    | @frame F e₁ e₂ _ hs' =>
      cases F <;> cases ht
      exact Step.not_value hs' hv

/-- **Progress.** Let `exn` be the exception type. A closed term of type `A` is final, that is a
value or an uncaught exception `raise v` with `v` a value, or it takes a step. -/
theorem progress {exn : Ty} {e : Term} {A : Ty} (h : HasType exn [] e A) :
    Final e ∨ ∃ e', Step e e' := by
  generalize hΓ : ([] : List Ty) = Γ at h
  induction h with
  | var hx =>
    subst hΓ
    simp at hx
  | lam _ _ => exact .inl (.inl (.lam _))
  | num => exact .inl (.inl (.num _))
  | app hf _ ihf iha =>
    rcases ihf hΓ with (hvf | ⟨vf, hvf, rfl⟩) | ⟨f', hf'⟩
    · rcases iha hΓ with (hva | ⟨va, hva, rfl⟩) | ⟨a', ha'⟩
      · obtain ⟨b, rfl⟩ := canonical_arr hvf hf
        exact .inr ⟨_, .beta hva⟩
      · exact .inr ⟨_, .propagate (F := .appR _) hva hvf (fun _ h => nomatch h)⟩
      · exact .inr ⟨_, .frame (F := .appR _) hvf ha'⟩
    · exact .inr ⟨_, .propagate (F := .appL _) hvf trivial (fun _ h => nomatch h)⟩
    · exact .inr ⟨_, .frame (F := .appL _) trivial hf'⟩
  | mul ha hb iha ihb =>
    rcases iha hΓ with (hva | ⟨va, hva, rfl⟩) | ⟨a', ha'⟩
    · rcases ihb hΓ with (hvb | ⟨vb, hvb, rfl⟩) | ⟨b', hb'⟩
      · obtain ⟨m, rfl⟩ := canonical_nat hva ha
        obtain ⟨n, rfl⟩ := canonical_nat hvb hb
        exact .inr ⟨_, .mul⟩
      · exact .inr ⟨_, .propagate (F := .mulR _) hvb hva (fun _ h => nomatch h)⟩
      · exact .inr ⟨_, .frame (F := .mulR _) hva hb'⟩
    · exact .inr ⟨_, .propagate (F := .mulL _) hva trivial (fun _ h => nomatch h)⟩
    · exact .inr ⟨_, .frame (F := .mulL _) trivial ha'⟩
  | ifz hc _ _ ihc _ _ =>
    rcases ihc hΓ with (hvc | ⟨vc, hvc, rfl⟩) | ⟨c', hc'⟩
    · obtain ⟨n, rfl⟩ := canonical_nat hvc hc
      cases n with
      | zero => exact .inr ⟨_, .ifzZero⟩
      | succ n => exact .inr ⟨_, .ifzSucc⟩
    · exact .inr ⟨_, .propagate (F := .ifz _ _) hvc trivial (fun _ h => nomatch h)⟩
    · exact .inr ⟨_, .frame (F := .ifz _ _) trivial hc'⟩
  | raise _ ih =>
    rcases ih hΓ with (hv | ⟨v, hv, rfl⟩) | ⟨e', he'⟩
    · exact .inl (.inr ⟨_, hv, rfl⟩)
    · exact .inr ⟨_, .propagate (F := .raise) hv trivial (fun _ h => nomatch h)⟩
    · exact .inr ⟨_, .frame (F := .raise) trivial he'⟩
  | tryWith _ _ ih₁ _ =>
    rcases ih₁ hΓ with (hv | ⟨v, hv, rfl⟩) | ⟨e', he'⟩
    · exact .inr ⟨_, .tryValue hv⟩
    · exact .inr ⟨_, .tryRaise hv⟩
    · exact .inr ⟨_, .frame (F := .tryWith _) trivial he'⟩

/-- **Preservation.** Let `exn` be the exception type and `Γ` a context. If `e` has type `A` in
`Γ` and `e` steps to `e'`, then `e'` has type `A` in `Γ`. -/
theorem preservation {exn : Ty} {Γ : List Ty} {e e' : Term} {A : Ty} (h : HasType exn Γ e A)
    (hs : Step e e') : HasType exn Γ e' A := by
  induction hs generalizing A with
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
  | @propagate F v _ _ hh =>
    cases F with
    | appL a =>
      cases h with
      | app hf _ =>
        cases hf with
        | raise hr => exact .raise hr
    | appR f =>
      cases h with
      | app _ ha =>
        cases ha with
        | raise hr => exact .raise hr
    | mulL b =>
      cases h with
      | mul ha _ =>
        cases ha with
        | raise hr => exact .raise hr
    | mulR a =>
      cases h with
      | mul _ hb =>
        cases hb with
        | raise hr => exact .raise hr
    | ifz t e =>
      cases h with
      | ifz hc _ _ =>
        cases hc with
        | raise hr => exact .raise hr
    | raise =>
      cases h with
      | raise hr =>
        cases hr with
        | raise hr' => exact .raise hr'
    | tryWith h' => exact absurd rfl (hh h')
  | tryValue _ =>
    cases h with
    | tryWith h₁ _ => exact h₁
  | tryRaise _ =>
    cases h with
    | tryWith h₁ h₂ =>
      cases h₁ with
      | raise hr => exact h₂.instantiate hr
  | @frame F e₁ e₂ _ _ ih =>
    cases F with
    | appL a =>
      cases h with
      | app hf ha => exact .app (ih hf) ha
    | appR f =>
      cases h with
      | app hf ha => exact .app hf (ih ha)
    | mulL b =>
      cases h with
      | mul ha hb => exact .mul (ih ha) hb
    | mulR a =>
      cases h with
      | mul ha hb => exact .mul ha (ih hb)
    | ifz t e =>
      cases h with
      | ifz hc ht he => exact .ifz (ih hc) ht he
    | raise =>
      cases h with
      | raise hr => exact .raise (ih hr)
    | tryWith h' =>
      cases h with
      | tryWith h₁ h₂ => exact .tryWith (ih h₁) h₂

/-! ### Safety through the schema -/

/-- **Typed terms reach only final or reducible terms.** Let `exn` be the exception type. Every
term reachable in any number of steps from a closed term of type `A` is final or takes a step. -/
theorem final_or_step {exn : Ty} {e e' : Term} {A : Ty} (h : HasType exn [] e A)
    (hr : Relation.ReflTransGen Step e e') : Final e' ∨ ∃ e'', Step e' e'' := by
  exact TypeSafety.final_or_step_of_reflTransGen Step Final (fun e A => HasType exn [] e A)
    (fun he => progress he) (fun _ _ _ hs he => preservation he hs) h hr

/-- **Typed terms never get stuck.** Let `exn` be the exception type. No term reachable in any
number of steps from a closed term of type `A` is a normal form that is not final. -/
theorem not_stuck {exn : Ty} {e e' : Term} {A : Ty} (h : HasType exn [] e A)
    (hr : Relation.ReflTransGen Step e e') : ¬ (¬ Final e' ∧ Relation.Normal Step e') := by
  exact TypeSafety.not_stuck_of_reflTransGen Step Final (fun e A => HasType exn [] e A)
    (fun he => progress he) (fun _ _ _ hs he => preservation he hs) h hr

/-- **Syntactic soundness.** Let `exn` be the exception type. Every term reachable in any number
of steps from a closed term of type `A` has type `A`, and is final or takes a step; in particular
a final term it reaches, a value or an uncaught exception `raise v`, has type `A`. This is Wright
and Felleisen's Theorem 5.10 for every reachable term, specialized to one anonymous exception. -/
theorem hasType_and_final_or_step {exn : Ty} {e e' : Term} {A : Ty} (h : HasType exn [] e A)
    (hr : Relation.ReflTransGen Step e e') :
    HasType exn [] e' A ∧ (Final e' ∨ ∃ e'', Step e' e'') := by
  have hp : Relation.Preserves Step (HasType exn [] · A) := fun _ _ hs he => preservation he hs
  exact ⟨Relation.preserves_reflTransGen_iff.mpr hp hr h, final_or_step h hr⟩

/-- **The calculus with exceptions has the structural properties.** For every exception type
`exn`, the typing judgment satisfies `TypeSafety.StructuralTyping` when binding adds a new
innermost variable, instantiation is `Term.instantiate`, a context `Γ` extends to `Θ ++ Γ` for
every block `Θ` of new innermost variables, and weakening raises every free variable by the
difference of the context lengths. -/
theorem structuralTyping (exn : Ty) :
    TypeSafety.StructuralTyping (HasType exn) (fun Γ (_ : Unit) A => A :: Γ)
      (fun t (_ : Unit) s => t.instantiate s) (fun Γ Δ => ∃ Θ, Δ = Θ ++ Γ)
      (fun Γ Δ t => t.rename (· + (Δ.length - Γ.length))) := by
  refine ⟨fun hbody hs => HasType.instantiate hbody hs, ?_⟩
  rintro Γ Δ t A ⟨Θ, rfl⟩ ht
  refine ht.rename fun x B hx => ?_
  rw [List.length_append, Nat.add_sub_cancel,
    List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel]
  exact hx

end Cslib.Languages.LambdaCalculus.Exceptions
