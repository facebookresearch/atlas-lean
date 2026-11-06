/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Truth-table semantics and soundness of natural deduction
-/
module

public import Cslib.Logics.Propositional.NaturalDeduction.Theory

/-!
# Truth-table semantics and soundness of natural deduction

Upstream CSLib's natural deduction (`Cslib.Logic.PL.Theory.Derivation`) has the
introduction and elimination rules of *minimal* logic only.  Falsum is not a
connective: under `[Bot Atom]` the proposition `⊥` is the atom `.atom ⊥`, and
intuitionistic or classical reasoning comes from axioms in the theory `T`
(`Theory.IPL`, `Theory.CPL`, or any `T` with an `IsClassical` instance).

This file interprets propositions in `Bool` and proves soundness of every
derivation, for every theory, against the valuations that satisfy that theory.

## Main definitions

- `Proposition.evalBool v A` : the truth-table value of `A` under a valuation
  `v : Atom → Bool` of the atoms.
- `Theory.BoolEntails T Γ A` : every valuation that makes all of `T` and all of
  `Γ` true makes `A` true.

## Main results

- `Theory.Derivation.boolSound`, `DerivableIn.boolSound` : soundness.  A
  `T`-derivation of `Γ ⊢ A` gives `T.BoolEntails Γ A`.
- `evalBool_of_mem_ipl`, `evalBool_of_mem_cpl` : the axioms of `IPL` and `CPL`
  are true under every valuation with `v ⊥ = false`.
- `DerivableIn.evalBool_of_cpl` : every sequent derivable in classical logic
  `CPL` is a tautology, read with `⊥` false.
- `not_derivableIn_cpl_bot`, `not_derivableIn_cpl_atom` : `CPL` derives neither
  falsum nor any atom.

## Implementation notes

The valuation is arbitrary on the atom `⊥`.  Soundness holds for all
valuations satisfying `T`, so it needs no assumption on `v ⊥`.  The classical
reading of `⊥` as false enters only through the `IPL`/`CPL` corollaries.  The
names avoid upstream PR leanprover/cslib#93 (Heyting-algebra semantics,
`Valuation.pInterpret`, `Theory.Derivation.sound`), whose soundness theorem
would specialise to this one at the Boolean algebra `Bool`.
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u}

/-! ### Truth-table evaluation -/

/-- **Truth-table evaluation.** Given a Boolean valuation $v$ of the atoms, the truth value of a
proposition is computed recursively: an atom $x$ has value $v(x)$, $A \wedge B$ is true iff both
$A$ and $B$ are, $A \vee B$ is true iff at least one of them is, and $A \to B$ is true iff $A$ is
false or $B$ is true. Falsum $\bot$, when present, is itself an atom, so its value $v(\bot)$ is
part of the valuation and need not be false. -/
def Proposition.evalBool (v : Atom → Bool) : Proposition Atom → Bool
  | atom x => v x
  | and A B => A.evalBool v && B.evalBool v
  | or A B => A.evalBool v || B.evalBool v
  | imp A B => !A.evalBool v || B.evalBool v

namespace Proposition

variable {v : Atom → Bool} {A B : Proposition Atom}

@[simp]
theorem evalBool_atom (x : Atom) : (atom x : Proposition Atom).evalBool v = v x := rfl

@[simp]
theorem evalBool_and : (A ∧ B).evalBool v = (A.evalBool v && B.evalBool v) := rfl

@[simp]
theorem evalBool_or : (A ∨ B).evalBool v = (A.evalBool v || B.evalBool v) := rfl

@[simp]
theorem evalBool_imp : (A → B).evalBool v = (!A.evalBool v || B.evalBool v) := rfl

@[simp]
theorem evalBool_bot [Bot Atom] : (⊥ : Proposition Atom).evalBool v = v ⊥ := rfl

/-- **Truth value of a negation.** Suppose the atoms include a distinguished atom $\bot$, and let
$v$ be a Boolean valuation of the atoms with $v(\bot) = \mathrm{false}$. Then for every proposition
$A$, the truth-table value under $v$ of $\neg A$, defined as $A \to \bot$, is the Boolean negation
of the truth-table value of $A$ under $v$. -/
theorem evalBool_neg [Bot Atom] (hv : v ⊥ = false) :
    (¬A : Proposition Atom).evalBool v = !A.evalBool v := by
  change (!A.evalBool v || v ⊥) = !A.evalBool v
  simp [hv]

end Proposition

/-! ### Semantic consequence -/

/-- **Truth-table consequence.** Let $T$ be a theory (a set of propositions), $\Gamma$ a context
(a finite set of propositions) and $A$ a proposition. Then $A$ is a truth-table consequence of
$\Gamma$ in $T$ when every Boolean valuation of the atoms under which all members of $T$ and all
members of $\Gamma$ evaluate to true also makes $A$ evaluate to true. -/
def Theory.BoolEntails (T : Theory Atom) (Γ : Ctx Atom) (A : Proposition Atom) : Prop :=
  ∀ v : Atom → Bool, (∀ B ∈ T, B.evalBool v = true) → (∀ B ∈ Γ, B.evalBool v = true) →
    A.evalBool v = true

/-! ### Soundness -/

variable [DecidableEq Atom] {T : Theory Atom}

/-- **Soundness of natural deduction for truth tables.** Let $T$ be a theory, $\Gamma$ a context and
$A$ a proposition. For every natural-deduction derivation of $\Gamma \vdash A$ with axioms from $T$,
every Boolean valuation of the atoms that makes all members of $T$ and of $\Gamma$ true makes $A$
true. -/
theorem Theory.Derivation.boolSound {Γ : Ctx Atom} {A : Proposition Atom}
    (D : T.Derivation Γ A) : T.BoolEntails Γ A := by
  intro v hT
  induction D with
  | ax hA => exact fun _ ↦ hT _ hA
  | ass hA => exact fun hΓ ↦ hΓ _ hA
  | andI _ _ ih₁ ih₂ =>
    intro hΓ
    simp [ih₁ hΓ, ih₂ hΓ]
  | andE₁ _ ih =>
    intro hΓ
    have h := ih hΓ
    simp only [evalBool_and, Bool.and_eq_true] at h
    exact h.1
  | andE₂ _ ih =>
    intro hΓ
    have h := ih hΓ
    simp only [evalBool_and, Bool.and_eq_true] at h
    exact h.2
  | orI₁ _ ih =>
    intro hΓ
    simp [ih hΓ]
  | orI₂ _ ih =>
    intro hΓ
    simp [ih hΓ]
  | @orE Γ A B C _ _ _ ih ih₁ ih₂ =>
    intro hΓ
    have h := ih hΓ
    simp only [evalBool_or, Bool.or_eq_true] at h
    rcases h with hA | hB
    · exact ih₁ fun X hX ↦ by
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact hA
        · exact hΓ X hX
    · exact ih₂ fun X hX ↦ by
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact hB
        · exact hΓ X hX
  | @implI A B Γ _ ih =>
    intro hΓ
    cases hA : A.evalBool v
    · simp [hA]
    · have hB : B.evalBool v = true := ih fun X hX ↦ by
        rcases Finset.mem_insert.mp hX with rfl | hX
        · exact hA
        · exact hΓ X hX
      simp [hB]
  | implE _ _ ih₁ ih₂ =>
    intro hΓ
    have himp := ih₁ hΓ
    have hA := ih₂ hΓ
    simpa [hA] using himp

/-- **Truth-table soundness of derivability.** Let $T$ be a theory, $\Gamma$ a context and $A$ a
proposition. If the sequent $\Gamma \vdash A$ is derivable in natural deduction with axioms from
$T$, then $A$ is a truth-table consequence of $\Gamma$ in $T$: every Boolean valuation of the
atoms that makes all members of $T$ and of $\Gamma$ true makes $A$ true. -/
theorem DerivableIn.boolSound {Γ : Ctx Atom} {A : Proposition Atom}
    (h : DerivableIn T (Γ ⊢ A)) : T.BoolEntails Γ A :=
  h.elim fun D ↦ Theory.Derivation.boolSound D

/-! ### Intuitionistic and classical axioms -/

section Classical

variable [Bot Atom] {v : Atom → Bool}

omit [DecidableEq Atom] in
/-- **Ex falso is true when falsum is false.** Suppose the atoms include a distinguished atom
$\bot$, and let $v$ be a Boolean valuation of the atoms with $v(\bot) = \mathrm{false}$. Then every
instance $\bot \to B$ of ex falso, that is every axiom of intuitionistic propositional logic, is
true under $v$. -/
theorem evalBool_of_mem_ipl (hv : v ⊥ = false) {A : Proposition Atom}
    (hA : A ∈ IPL Atom) : A.evalBool v = true := by
  obtain ⟨B, rfl⟩ := hA
  simp [hv]

omit [DecidableEq Atom] in
/-- **Double-negation elimination is true when falsum is false.** Suppose the atoms include a
distinguished atom $\bot$, and let $v$ be a Boolean valuation of the atoms with
$v(\bot) = \mathrm{false}$. Then every instance $\neg\neg B \to B$ of double-negation elimination,
that is every axiom of classical propositional logic, is true under $v$. -/
theorem evalBool_of_mem_cpl (hv : v ⊥ = false) {A : Proposition Atom}
    (hA : A ∈ CPL Atom) : A.evalBool v = true := by
  obtain ⟨B, rfl⟩ := hA
  change (!(!(!B.evalBool v || v ⊥) || v ⊥) || B.evalBool v) = true
  cases B.evalBool v <;> simp [hv]

/-- **Classical derivability implies truth under valuations with false falsum.** Suppose the atoms
include a distinguished atom $\bot$, and let $v$ be a Boolean valuation of the atoms with
$v(\bot) = \mathrm{false}$. If the sequent $\Gamma \vdash A$ is derivable in classical propositional
logic (natural deduction whose axioms are all instances $\neg\neg B \to B$ of double-negation
elimination) and every member of $\Gamma$ is true under $v$, then $A$ is true under $v$. -/
theorem DerivableIn.evalBool_of_cpl {Γ : Ctx Atom} {A : Proposition Atom}
    (h : DerivableIn (CPL Atom) (Γ ⊢ A)) (hv : v ⊥ = false)
    (hΓ : ∀ B ∈ Γ, B.evalBool v = true) : A.evalBool v = true :=
  DerivableIn.boolSound h v (fun _ hB ↦ evalBool_of_mem_cpl hv hB) hΓ

/-- **Intuitionistic derivability implies truth under valuations with false falsum.** Suppose the
atoms include a distinguished atom $\bot$, and let $v$ be a Boolean valuation of the atoms with
$v(\bot) = \mathrm{false}$. If the sequent $\Gamma \vdash A$ is derivable in intuitionistic
propositional logic (natural deduction whose axioms are all instances $\bot \to B$ of ex falso)
and every member of $\Gamma$ is true under $v$, then $A$ is true under $v$. -/
theorem DerivableIn.evalBool_of_ipl {Γ : Ctx Atom} {A : Proposition Atom}
    (h : DerivableIn (IPL Atom) (Γ ⊢ A)) (hv : v ⊥ = false)
    (hΓ : ∀ B ∈ Γ, B.evalBool v = true) : A.evalBool v = true :=
  DerivableIn.boolSound h v (fun _ hB ↦ evalBool_of_mem_ipl hv hB) hΓ

/-- **Consistency of classical propositional logic.** For every type of atoms with a designated
atom $\bot$, the proposition $\bot$ is not derivable from the empty context in natural deduction
over the classical theory, whose axioms are all instances $\neg\neg A \to A$ of double-negation
elimination, where $\neg A$ abbreviates $A \to \bot$. -/
theorem not_derivableIn_cpl_bot : ¬ DerivableIn (CPL Atom) (⊥ : Proposition Atom) := by
  intro h
  have := DerivableIn.evalBool_of_cpl (v := fun _ ↦ false) h rfl (by simp)
  simp at this

/-- **Classical logic proves no atom.** Suppose the atoms include a distinguished atom $\bot$. For
every atom $x$, including $\bot$, the proposition $x$ is not derivable from the empty context in
classical propositional logic (natural deduction whose axioms are all instances $\neg\neg B \to B$
of double-negation elimination). -/
theorem not_derivableIn_cpl_atom (x : Atom) :
    ¬ DerivableIn (CPL Atom) (atom x : Proposition Atom) := by
  intro h
  have := DerivableIn.evalBool_of_cpl (v := fun _ ↦ false) h rfl (by simp)
  simp at this

end Classical

end Cslib.Logic.PL
