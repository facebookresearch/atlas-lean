/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Functional completeness of propositional connectives
-/
module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Completeness

/-!
# Functional completeness of propositional connectives

Every Boolean function of finitely many atoms is the truth table of a
proposition, and `→` with `⊥` alone already suffice.

As elsewhere in this directory, `⊥` is upstream CSLib's atom `.atom ⊥`, read as
false; `⊤` is written `⊥ → ⊥`.

## Main definitions

- `Proposition.shannon xs f` : the Shannon expansion of `f : (Atom → Bool) → Bool`
  over the atoms of `xs`: `(x ∧ f[x := ⊤]) ∨ (¬x ∧ f[x := ⊥])` for each `x`, then
  `⊤` or `⊥` once no atom is left.
- `Proposition.IsImpBot A` : `A` is built from atoms with `→` only (`⊥` being an
  atom).
- `Proposition.toImpBot A` : `A ∧ B` as `(A → (B → ⊥)) → ⊥` and `A ∨ B` as
  `(A → ⊥) → B`.

## Main results

- `Proposition.evalBool_shannon` : if `f` depends only on the atoms of `xs`, then
  `shannon xs f` evaluates to `f v` under every `v` with `⊥` false.
- `exists_evalBool_eq` (functional completeness) and
  `exists_isImpBot_evalBool_eq` (the same with `→` and `⊥` only).
- `Proposition.evalBool_toImpBot`, `derivableIn_cpl_toImpBot_iff` : the
  translation preserves truth values when `⊥` is false and classical
  derivability.

## References

- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §1.3 (functional
  completeness).
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

open Proposition Theory InferenceSystem

variable {Atom : Type u} [Bot Atom]

section Shannon

variable [DecidableEq Atom]

namespace Proposition

/-- **Shannon expansion.** Let $f$ assign a truth value to every valuation of the atoms. The
Shannon expansion $S(\ell, f)$ of $f$ over a list $\ell$ of atoms is defined by recursion on
$\ell$. For the empty list it is $\bot \to \bot$ if $f$ is true at the valuation that makes every
atom false, and $\bot$ otherwise. For the list $x \cdot \ell$ with head $x$ and tail $\ell$,
$$
S(x \cdot \ell, f) = (x \wedge S(\ell, f_1)) \vee (\neg x \wedge S(\ell, f_0)),
$$
where $\neg x$ is $x \to \bot$, and $f_1(v) = f(v[x \mapsto \mathrm{true}])$ and
$f_0(v) = f(v[x \mapsto \mathrm{false}])$, with $v[x \mapsto b]$ the valuation $v$ changed at $x$
to $b$. -/
def shannon : List Atom → ((Atom → Bool) → Bool) → Proposition Atom
  | [], f => if f (fun _ ↦ false) then (⊥ → ⊥ : Proposition Atom) else ⊥
  | x :: xs, f =>
    or (and (atom x) (shannon xs fun v ↦ f (Function.update v x true)))
      (and (¬(atom x) : Proposition Atom) (shannon xs fun v ↦ f (Function.update v x false)))

/-- **Correctness of the Shannon expansion.** Let $x_1, \dots, x_n$ be a list of atoms and let
$f$ assign a truth value to every valuation of the atoms, such that $f(v) = f(w)$ whenever $v$
and $w$ agree on $x_1, \dots, x_n$. Then for every valuation $v$ that makes $\bot$ false, the
Shannon expansion of $f$ over $x_1, \dots, x_n$ has truth value $f(v)$ under $v$. -/
theorem evalBool_shannon {xs : List Atom} {f : (Atom → Bool) → Bool}
    (hf : ∀ v w : Atom → Bool, (∀ a ∈ xs, v a = w a) → f v = f w) {v : Atom → Bool}
    (hv : v ⊥ = false) : (shannon xs f).evalBool v = f v := by
  induction xs generalizing f with
  | nil =>
    have hc : f v = f (fun _ ↦ false) := hf _ _ fun _ h ↦ absurd h List.not_mem_nil
    cases hfv : f (fun _ ↦ false) <;> simp [shannon, hfv, hc, hv]
  | cons x xs ih =>
    have hg : ∀ b, ∀ v w : Atom → Bool, (∀ a ∈ xs, v a = w a) →
        f (Function.update v x b) = f (Function.update w x b) := by
      intro b v w hvw
      apply hf
      intro a ha
      by_cases hax : a = x
      · subst hax
        simp
      · simp only [Function.update_of_ne hax]
        exact hvw a ((List.mem_cons.mp ha).resolve_left hax)
    have h1 := ih (f := fun v ↦ f (Function.update v x true)) (hg true)
    have h0 := ih (f := fun v ↦ f (Function.update v x false)) (hg false)
    have hneg : (¬(atom x) : Proposition Atom).evalBool v = !v x := by
      rw [evalBool_neg hv]
      rfl
    have hfv : f (Function.update v x (v x)) = f v := by rw [Function.update_eq_self]
    simp only [shannon, evalBool]
    rw [hneg, h1, h0]
    generalize v x = b at hfv ⊢
    cases b <;> simpa using hfv

end Proposition

/-- **Functional completeness**: every Boolean function of the atoms in a finite list is the
truth table, on valuations with `⊥` false, of some proposition. -/
theorem exists_evalBool_eq (xs : List Atom) (f : (Atom → Bool) → Bool)
    (hf : ∀ v w : Atom → Bool, (∀ a ∈ xs, v a = w a) → f v = f w) :
    ∃ A : Proposition Atom, ∀ v : Atom → Bool, v ⊥ = false → A.evalBool v = f v :=
  ⟨shannon xs f, fun _ hv ↦ evalBool_shannon hf hv⟩

end Shannon

/-! ### Implication and falsum suffice -/

namespace Proposition

/-- **Propositions built from $\to$ and $\bot$.** A proposition is built from $\to$ and $\bot$
when it contains no conjunction and no disjunction: every atom (including $\bot$, which is an
atom) is, and $A \to B$ is exactly when both $A$ and $B$ are. -/
def IsImpBot : Proposition Atom → Prop
  | atom _ => True
  | and _ _ => False
  | or _ _ => False
  | imp A B => IsImpBot A ∧ IsImpBot B

/-- **Translation into $\to$ and $\bot$.** The translation $A^*$ of a proposition $A$ is defined
by recursion on $A$: each atom is unchanged, $(A \to B)^* = A^* \to B^*$,
$(A \wedge B)^* = (A^* \to (B^* \to \bot)) \to \bot$ and $(A \vee B)^* = (A^* \to \bot) \to B^*$. -/
def toImpBot : Proposition Atom → Proposition Atom
  | atom a => atom a
  | and A B => imp (imp (toImpBot A) (imp (toImpBot B) ⊥)) ⊥
  | or A B => imp (imp (toImpBot A) ⊥) (toImpBot B)
  | imp A B => imp (toImpBot A) (toImpBot B)

theorem isImpBot_toImpBot (A : Proposition Atom) : IsImpBot (toImpBot A) := by
  induction A with
  | atom a => trivial
  | and A B ihA ihB => exact ⟨⟨ihA, ihB, trivial⟩, trivial⟩
  | or A B ihA ihB => exact ⟨⟨ihA, trivial⟩, ihB⟩
  | imp A B ihA ihB => exact ⟨ihA, ihB⟩

/-- **The translation into $\to$ and $\bot$ preserves truth values.** For every proposition $A$
and every valuation $v$ that makes $\bot$ false, the translation of $A$ into $\to$ and $\bot$
has the same truth value under $v$ as $A$. -/
theorem evalBool_toImpBot (A : Proposition Atom) {v : Atom → Bool} (hv : v ⊥ = false) :
    (toImpBot A).evalBool v = A.evalBool v := by
  induction A with
  | atom a => rfl
  | imp A B ihA ihB => simp only [toImpBot, evalBool, ihA, ihB]
  | and A B ihA ihB | or A B ihA ihB =>
    simp only [toImpBot, evalBool, ihA, ihB]
    cases A.evalBool v <;> cases B.evalBool v <;> simp [hv]

end Proposition

/-- **Functional completeness of `→` and `⊥`**: every Boolean function of the atoms in a
finite list is the truth table, on valuations with `⊥` false, of a proposition built with
`→` alone. -/
theorem exists_isImpBot_evalBool_eq [DecidableEq Atom] (xs : List Atom) (f : (Atom → Bool) → Bool)
    (hf : ∀ v w : Atom → Bool, (∀ a ∈ xs, v a = w a) → f v = f w) :
    ∃ A : Proposition Atom, A.IsImpBot ∧
      ∀ v : Atom → Bool, v ⊥ = false → A.evalBool v = f v :=
  ⟨toImpBot (shannon xs f), isImpBot_toImpBot _, fun _ hv ↦ by
    rw [evalBool_toImpBot _ hv, evalBool_shannon hf hv]⟩

/-- **The translation into $\to$ and $\bot$ preserves and reflects classical derivability.**
For every proposition $A$, let $A^*$ be its translation into $\to$ and $\bot$, which keeps atoms
and implications and recursively replaces each $B \wedge C$ by $(B \to (C \to \bot)) \to \bot$
and each $B \vee C$ by $(B \to \bot) \to C$. Then $A^*$ is derivable from no hypotheses in
classical propositional logic if and only if $A$ is. -/
theorem derivableIn_cpl_toImpBot_iff [DecidableEq Atom] (A : Proposition Atom) :
    DerivableIn (CPL Atom) A.toImpBot ↔ DerivableIn (CPL Atom) A := by
  rw [DerivableIn.iff_derivableIn_empty, DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff,
    derivableIn_cpl_iff]
  exact forall_congr' fun v ↦ imp_congr_right fun hv ↦ by rw [evalBool_toImpBot A hv]

end Cslib.Logic.PL
