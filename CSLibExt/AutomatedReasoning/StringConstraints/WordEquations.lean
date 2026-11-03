/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.Syntax
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Ordinary word equations

A word equation has two finite lists of constants and variables. Substitution
replaces every occurrence of a variable by the same finite word, possibly empty.
Unlike the larger `Term` language, this syntax has no `hom` operation. Its
embedding into `Term` preserves evaluation, so the two semantics are connected.

Ground equations have an executable Boolean decider. Pattern matching against a
fixed target is equivalent to matching with all variable images bounded by the
target length, after unused images are replaced by `[]`. Over `Fin n`, an
arbitrary equation or system has a solution iff it has one at some finite global
bound. That existential result is not a general UNSAT decision procedure.

The bounded SAT translation is separate, in `BitBlast`; this file does not use
it or the noncomputable specification in `Bounded`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.AutomatedReasoning.StringConstraints

variable {α V : Type*}

/-- Substitute words for variables in a word over constants and variables. -/
def evalWord (σ : V → List α) (w : List (α ⊕ V)) : List α :=
  w.flatMap (Sum.elim (fun a => [a]) σ)

/-- Embed an ordinary word in the larger string-constraint term language. -/
def wordTerm : List (α ⊕ V) → Term α V
  | [] => .const []
  | Sum.inl a :: w => .append (.const [a]) (wordTerm w)
  | Sum.inr i :: w => .append (.var i) (wordTerm w)

/-- The embedding preserves substitution semantics. -/
@[simp] theorem eval_wordTerm (σ : V → List α) (w : List (α ⊕ V)) :
    eval σ (wordTerm w) = evalWord σ w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [wordTerm, evalWord, eval, ih]

/-- An ordinary word equation, with no morphisms or language-membership atoms. -/
structure WordEq (α V : Type*) where
  lhs : List (α ⊕ V)
  rhs : List (α ⊕ V)

/-- A substitution solves a word equation when the substituted sides agree. -/
def WordEq.Satisfies (σ : V → List α) (e : WordEq α V) : Prop :=
  evalWord σ e.lhs = evalWord σ e.rhs

/-- View an ordinary word equation as a string-constraint formula. -/
def WordEq.toFormula (e : WordEq α V) : Formula α V :=
  .atom (.eq (wordTerm e.lhs) (wordTerm e.rhs))

/-- The formula embedding preserves satisfaction. -/
@[simp] theorem WordEq.sat_toFormula (σ : V → List α) (e : WordEq α V) :
    Sat σ e.toFormula ↔ e.Satisfies σ := by
  simp [WordEq.toFormula, SatAtom, WordEq.Satisfies]

/-- Evaluation depends only on variables that occur in the word. -/
theorem evalWord_eq_of_agree_on_vars {σ τ : V → List α} {w : List (α ⊕ V)}
    (h : ∀ i, Sum.inr i ∈ w → σ i = τ i) : evalWord σ w = evalWord τ w := by
  apply List.flatMap_congr
  intro a ha
  cases a with
  | inl a => rfl
  | inr i => exact h i ha

/-- Each occurring variable contributes a contiguous block, so its length cannot
exceed the length of the evaluated word, even when substitutions may be empty. -/
theorem length_le_evalWord_of_mem (σ : V → List α) {w : List (α ⊕ V)} {i : V}
    (hi : Sum.inr i ∈ w) : (σ i).length ≤ (evalWord σ w).length := by
  exact (List.infix_of_mem_flatten
    (List.mem_map_of_mem (f := Sum.elim (fun a => [a]) σ) hi)).length_le

/-- Retain the images of occurring variables and replace every unused image by
`[]`. Only equality of variables, not equality of alphabet symbols, is needed. -/
def normalizeWordSubst [DecidableEq V] (σ : V → List α) (w : List (α ⊕ V)) :
    V → List α :=
  fun i => if i ∈ w.filterMap (Sum.elim (fun _ => none) some) then σ i else []

/-- Normalization preserves the image of every occurring variable. -/
theorem normalizeWordSubst_of_mem [DecidableEq V] (σ : V → List α)
    {w : List (α ⊕ V)} {i : V} (hi : Sum.inr i ∈ w) :
    normalizeWordSubst σ w i = σ i := by
  apply ite_eq_left
  exact List.mem_filterMap.mpr ⟨Sum.inr i, hi, rfl⟩

/-- Every variable absent from the word has empty normalized image. -/
theorem normalizeWordSubst_of_not_mem [DecidableEq V] (σ : V → List α)
    {w : List (α ⊕ V)} {i : V} (hi : Sum.inr i ∉ w) :
    normalizeWordSubst σ w i = [] := by
  apply ite_eq_right
  intro h
  obtain ⟨a, ha, hai⟩ := List.mem_filterMap.mp h
  cases a with
  | inl a => cases hai
  | inr j =>
    cases Option.some.inj hai
    exact hi ha

/-- Removing unused images does not change the evaluated word. -/
@[simp] theorem evalWord_normalizeWordSubst [DecidableEq V] (σ : V → List α)
    (w : List (α ⊕ V)) : evalWord (normalizeWordSubst σ w) w = evalWord σ w := by
  exact evalWord_eq_of_agree_on_vars (fun _ hi => normalizeWordSubst_of_mem σ hi)

/-- After normalization, every variable image, including unused ones, is
bounded by the length of the original evaluation. -/
theorem length_normalizeWordSubst_le [DecidableEq V] (σ : V → List α)
    (w : List (α ⊕ V)) (i : V) :
    (normalizeWordSubst σ w i).length ≤ (evalWord σ w).length := by
  unfold normalizeWordSubst
  split
  next h =>
    obtain ⟨a, ha, hai⟩ := List.mem_filterMap.mp h
    cases a with
    | inl a => cases hai
    | inr j =>
      cases Option.some.inj hai
      exact length_le_evalWord_of_mem σ ha
  next => exact Nat.zero_le _

/-- Matching a pattern against a fixed target loses no solutions by bounding
ALL variable images by the target length. Unused variables are normalized to
`[]`; an arbitrary unnormalized solution need not obey this bound. -/
theorem patternMatch_iff_bounded {n : ℕ} (w : List (α ⊕ Fin n)) (target : List α) :
    (∃ σ : Fin n → List α, evalWord σ w = target) ↔
      ∃ σ : Fin n → List α, (∀ i, (σ i).length ≤ target.length) ∧
        evalWord σ w = target := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨normalizeWordSubst σ w, ?_, ?_⟩
    · intro i
      simpa only [hσ] using length_normalizeWordSubst_le σ w i
    · simpa only [evalWord_normalizeWordSubst] using hσ
  · rintro ⟨σ, _, hσ⟩
    exact ⟨σ, hσ⟩

/-- Executable satisfaction test for a ground equation. Since the variable
type is `Empty`, no substitution search is required. -/
def WordEq.groundSatB [DecidableEq α] (e : WordEq α Empty) : Bool :=
  decide (evalWord Empty.elim e.lhs = evalWord Empty.elim e.rhs)

/-- The ground test agrees with satisfaction under any substitution. -/
theorem WordEq.groundSatB_eq_true_iff [DecidableEq α] (e : WordEq α Empty)
    (σ : Empty → List α) : e.groundSatB = true ↔ e.Satisfies σ := by
  have hσ : σ = Empty.elim := funext (fun i => i.elim)
  subst σ
  simp [WordEq.groundSatB, WordEq.Satisfies]

/-- The executable ground test decides existence of a solution, not just
satisfaction of one guessed substitution. -/
theorem WordEq.groundSatB_iff [DecidableEq α] (e : WordEq α Empty) :
    e.groundSatB = true ↔ ∃ σ : Empty → List α, e.Satisfies σ := by
  constructor
  · intro h
    exact ⟨Empty.elim, (e.groundSatB_eq_true_iff Empty.elim).mp h⟩
  · rintro ⟨σ, hσ⟩
    exact (e.groundSatB_eq_true_iff σ).mpr hσ

/-- A system over finitely many variables has a solution iff one substitution
solves every equation at some finite global length bound. The witness bound is
obtained from the solution; this supplies no terminating general UNSAT test. -/
theorem wordSystem_satisfiable_iff_exists_bound {n : ℕ} (es : List (WordEq α (Fin n))) :
    (∃ σ : Fin n → List α, ∀ e ∈ es, e.Satisfies σ) ↔
      ∃ B : ℕ, ∃ σ : Fin n → List α, (∀ i, (σ i).length ≤ B) ∧
        ∀ e ∈ es, e.Satisfies σ := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨(List.ofFn (fun i => (σ i).length)).sum, σ, ?_, hσ⟩
    intro i
    exact List.le_sum_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · rintro ⟨_, σ, _, hσ⟩
    exact ⟨σ, hσ⟩

/-- An equation over `Fin n` is satisfiable iff it is satisfiable at some
finite global length bound. There is no equation-computable bound claimed. -/
theorem WordEq.satisfiable_iff_exists_bound {n : ℕ} (e : WordEq α (Fin n)) :
    (∃ σ : Fin n → List α, e.Satisfies σ) ↔
      ∃ B : ℕ, ∃ σ : Fin n → List α, (∀ i, (σ i).length ≤ B) ∧ e.Satisfies σ := by
  simpa only [List.mem_singleton, forall_eq] using
    wordSystem_satisfiable_iff_exists_bound [e]

end Cslib.AutomatedReasoning.StringConstraints
