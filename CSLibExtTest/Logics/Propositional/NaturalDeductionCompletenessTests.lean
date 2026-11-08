/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Completeness

@[expose] public section

/-!
# Tests for completeness and compactness of classical natural deduction

Derivations obtained from truth tables, refutations obtained from
countervaluations, model existence for a consistent set, and compactness on
finite unsatisfiable cores.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.NaturalDeductionCompleteness

open Cslib.Logic Cslib.Logic.PL Proposition Theory InferenceSystem

/-- Two ordinary atoms plus a separate falsum atom `⊥`. -/
inductive At where
  | falsum
  | x
  | y
  deriving DecidableEq

instance : Bot At := ⟨.falsum⟩

private def p : Proposition At := .atom .x
private def q : Proposition At := .atom .y

/-- Excluded middle, derived in `CPL` from its truth table. -/
example : DerivableIn (CPL At) (p ∨ ¬p : Proposition At) :=
  derivableIn_cpl_iff.mpr fun v hv _ ↦ by
    rw [evalBool_or, evalBool_neg hv]
    cases h : v .x <;> simp [p, h]

/-- Peirce's law, derived in `CPL` from its truth table. -/
example : DerivableIn (CPL At) (((p → q) → p) → p : Proposition At) :=
  derivableIn_cpl_iff.mpr fun v _ _ ↦ by
    cases h : v .x <;> simp [p, h]

/-- A contextual sequent: `¬q, p → q ⊢ ¬p` (modus tollens). -/
example : DerivableIn (CPL At) ({¬q, p → q} ⊢ (¬p : Proposition At)) :=
  derivableIn_cpl_iff.mpr fun v hv hΓ ↦ by
    have h1 := hΓ (¬q) (by simp)
    have h2 := hΓ (p → q) (by simp)
    rw [evalBool_neg hv] at h1 ⊢
    cases hx : v .x <;> cases hy : v .y <;> simp_all [p, q]

/-- Completeness is an equivalence: `p → q` is not derivable in `CPL`. -/
example : ¬ DerivableIn (CPL At) (p → q : Proposition At) := by
  rw [DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff]
  intro h
  have := h (fun a ↦ decide (a = .x)) rfl (by simp)
  simp [p, q] at this

/-- The theory-relative form: from the extra axiom `p`, `CPL ∪ {p}` derives `q → p`. -/
example : DerivableIn (CPL At ∪ {p} : Theory At) (q → p : Proposition At) := by
  have : IsClassical At (CPL At ∪ {p} : Theory At) :=
    ⟨fun A ↦ (IsClassical.dne (S := CPL At) A).weakTheory Set.subset_union_left⟩
  refine Theory.derivableIn_of_forall_evalBool fun v _ hT _ ↦ ?_
  have hp := hT p (Or.inr rfl)
  simp [hp]

/-- Model existence: `{p, ¬q}` is consistent relative to `IPL`, so it is satisfiable. -/
example : BoolSatisfiable ({p, ¬q} : Set (Proposition At)) := by
  have hcons : (IPL At).ConsistentWith {p, ¬q} := by
    intro Γ hΓ hder
    have := DerivableIn.evalBool_of_ipl (v := fun a ↦ decide (a = .x)) hder rfl
      (fun B hB ↦ by
        rcases hΓ hB with rfl | rfl
        · rfl
        · rfl)
    simp at this
  exact hcons.boolSatisfiable.mono Set.subset_union_right

/-- `{p, ¬p}` is unsatisfiable. -/
private theorem not_sat_core : ¬ BoolSatisfiable ({p, ¬p} : Set (Proposition At)) := by
  rintro ⟨v, hv, h⟩
  have h1 := h p (by simp)
  have h2 := h (¬p) (by simp)
  rw [evalBool_neg hv, h1] at h2
  exact absurd h2 (by decide)

/-- Compactness, used in the direction that turns a finite unsatisfiable core into the
unsatisfiability of a superset. -/
example (S : Set (Proposition At)) (hS : ({p, ¬p} : Set (Proposition At)) ⊆ S) :
    ¬ BoolSatisfiable S := fun h ↦
  not_sat_core (by simpa using boolSatisfiable_iff_forall_finset.mp h {p, ¬p} (by simpa using hS))

end CSLibExtTest.Logics.Propositional.NaturalDeductionCompleteness
