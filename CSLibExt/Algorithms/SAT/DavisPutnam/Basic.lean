/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Davis-Putnam variable elimination
-/
module

public import CSLibExt.Logics.Propositional.CNF.Resolution

/-!
# Davis-Putnam variable elimination

The Davis-Putnam procedure decides CNF satisfiability by eliminating one variable
at a time.  Eliminating `x` replaces every clause that mentions `x` by all
resolvents on `x` of a clause containing `x` positively with one containing it
negatively; clauses containing both `x` and `¬x` are always true and are dropped.
The result does not mention `x`, its other variables come from the input, and it
is satisfiable iff the input is.  After all variables are gone, a formula is
satisfiable iff it has no empty clause.

## Main definitions

- `CNF.eliminate x φ` : one elimination step.
- `CNF.eliminateAll xs φ` : eliminate the variables of `xs` in order.
- `CNF.davisPutnam φ` : eliminate every variable of `φ` (`CNF.varList φ`), then
  test for the empty clause.

## Main results

- `CNF.cnfSat_eliminate_iff` : elimination preserves satisfiability.
- `CNF.vars_eliminate_subset` : `(eliminate x φ).vars ⊆ φ.vars.erase x`.
- `CNF.davisPutnam_eq_true_iff` : `davisPutnam φ = true ↔ CNFSat φ`.

Cost: each step can square the number of clauses, so the procedure takes
exponential time and space in the worst case (the reason DPLL replaced it); no
cost theorem is claimed.

## References

- M. Davis, H. Putnam, *A computing procedure for quantification theory*,
  J. ACM 7(3), 1960, 201-215.
- U. Schöning, *Logic for Computer Scientists*, Birkhäuser 1989, §1.5.
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNF

/-- Clauses containing `x` positively and not negatively. -/
def posClauses (x : Nat) (φ : CNF) : CNF :=
  φ.filter fun C ↦ (x, true) ∈ C ∧ (x, false) ∉ C

/-- Clauses containing `x` negatively and not positively. -/
def negClauses (x : Nat) (φ : CNF) : CNF :=
  φ.filter fun C ↦ (x, false) ∈ C ∧ (x, true) ∉ C

/-- One Davis-Putnam step: keep the clauses that do not mention `x`, and add every resolvent
on `x` of a clause of `posClauses x φ` with one of `negClauses x φ` (computed once). Clauses
containing both `x` and `¬x` are dropped. -/
def eliminate (x : Nat) (φ : CNF) : CNF :=
  let neg := negClauses x φ
  φ.filter (fun C ↦ (x, true) ∉ C ∧ (x, false) ∉ C) ++
    (posClauses x φ).flatMap fun C ↦ neg.map fun D ↦ CNFClause.resolvent x C D

theorem mem_eliminate {x : Nat} {φ : CNF} {E : CNFClause} :
    E ∈ eliminate x φ ↔
      (E ∈ φ ∧ (x, true) ∉ E ∧ (x, false) ∉ E) ∨
      ∃ C ∈ φ, ((x, true) ∈ C ∧ (x, false) ∉ C) ∧
        ∃ D ∈ φ, ((x, false) ∈ D ∧ (x, true) ∉ D) ∧ CNFClause.resolvent x C D = E := by
  simp [eliminate, posClauses, negClauses, and_assoc]

/-- The resolvents added by `eliminate` do not mention `x`. -/
theorem fst_ne_of_mem_resolvent {x : Nat} {C D : CNFClause} (hC : (x, false) ∉ C)
    (hD : (x, true) ∉ D) {l : Nat × Bool} (hl : l ∈ CNFClause.resolvent x C D) : l.1 ≠ x := by
  obtain ⟨y, b⟩ := l
  rintro rfl
  rcases CNFClause.mem_resolvent.mp hl with ⟨hlC, hne⟩ | ⟨hlD, hne⟩
  · cases b
    · exact hC hlC
    · exact hne rfl
  · cases b
    · exact hne rfl
    · exact hD hlD

theorem vars_eliminate_subset (x : Nat) (φ : CNF) : (eliminate x φ).vars ⊆ φ.vars.erase x := by
  intro y hy
  obtain ⟨E, hE, b, hyE⟩ := mem_vars.mp hy
  rcases mem_eliminate.mp hE with ⟨hEφ, hxt, hxf⟩ | ⟨C, hCφ, ⟨-, hCf⟩, D, hDφ, ⟨-, hDt⟩, rfl⟩
  · refine Finset.mem_erase.mpr ⟨fun hyx ↦ ?_, mem_vars.mpr ⟨E, hEφ, b, hyE⟩⟩
    subst hyx
    cases b
    · exact hxf hyE
    · exact hxt hyE
  · refine Finset.mem_erase.mpr ⟨fst_ne_of_mem_resolvent hCf hDt hyE, ?_⟩
    rcases CNFClause.mem_resolvent.mp hyE with ⟨hlC, -⟩ | ⟨hlD, -⟩
    · exact mem_vars.mpr ⟨C, hCφ, b, hlC⟩
    · exact mem_vars.mpr ⟨D, hDφ, b, hlD⟩

theorem not_mem_vars_eliminate (x : Nat) (φ : CNF) : x ∉ (eliminate x φ).vars := fun h ↦
  (Finset.mem_erase.mp (vars_eliminate_subset x φ h)).1 rfl

/-- Soundness of a step: an assignment satisfying `φ` satisfies `eliminate x φ`. -/
theorem satisfies_eliminate {x : Nat} {φ : CNF} {σ : Nat → Bool} (h : φ.Satisfies σ) :
    (eliminate x φ).Satisfies σ := by
  intro E hE
  rcases mem_eliminate.mp hE with ⟨hEφ, -, -⟩ | ⟨C, hCφ, -, D, hDφ, -, rfl⟩
  · exact h E hEφ
  · exact CNFClause.satisfies_resolvent (h C hCφ) (h D hDφ)

/-- A clause satisfied by `σ` and not mentioning `x` stays satisfied when `x` changes. -/
private theorem clause_satisfies_update {x : Nat} {C : CNFClause} {σ : Nat → Bool} (b : Bool)
    (hx : ∀ l ∈ C, l.1 ≠ x) (h : C.Satisfies σ) : C.Satisfies (Function.update σ x b) := by
  obtain ⟨l, hl, hls⟩ := h
  refine ⟨l, hl, ?_⟩
  simp only [CNFLiteral.satisfies_def, Function.update_of_ne (hx l hl)] at hls ⊢
  exact hls

/-- Completeness of a step: from an assignment satisfying `eliminate x φ`, changing the value
of `x` alone gives one satisfying `φ`. -/
theorem exists_satisfies_update_of_satisfies_eliminate {x : Nat} {φ : CNF} {σ : Nat → Bool}
    (h : (eliminate x φ).Satisfies σ) : ∃ b, φ.Satisfies (Function.update σ x b) := by
  classical
  -- the clause `C` without its `x` literal
  let rest (C : CNFClause) : CNFClause := C.filter (· ≠ (x, true))
  have hkeep : ∀ E ∈ φ, (x, true) ∉ E → (x, false) ∉ E → ∀ b,
      E.Satisfies (Function.update σ x b) := by
    intro E hE ht hf b
    refine clause_satisfies_update b (fun l hl hlx ↦ ?_) (h E (mem_eliminate.mpr
      (Or.inl ⟨hE, ht, hf⟩)))
    obtain ⟨y, c⟩ := l
    simp only at hlx
    subst hlx
    cases c
    · exact hf hl
    · exact ht hl
  have htaut : ∀ E : CNFClause, (x, true) ∈ E → (x, false) ∈ E → ∀ τ : Nat → Bool,
      E.Satisfies τ := by
    intro E ht hf τ
    cases hτ : τ x
    · exact ⟨(x, false), hf, hτ⟩
    · exact ⟨(x, true), ht, hτ⟩
  by_cases hall : ∀ C ∈ φ, (x, true) ∈ C → (x, false) ∉ C → (rest C).Satisfies σ
  · -- every positive clause holds without `x`: set `x` false
    refine ⟨false, fun E hE ↦ ?_⟩
    by_cases ht : (x, true) ∈ E <;> by_cases hf : (x, false) ∈ E
    · exact htaut E ht hf _
    · obtain ⟨l, hl, hls⟩ := hall E hE ht hf
      obtain ⟨hlE, hlne⟩ := List.mem_filter.mp hl
      have hlx : l.1 ≠ x := by
        obtain ⟨y, c⟩ := l
        rintro rfl
        cases c
        · exact hf hlE
        · simp at hlne
      refine ⟨l, hlE, ?_⟩
      simp only [CNFLiteral.satisfies_def, Function.update_of_ne hlx] at hls ⊢
      exact hls
    · exact ⟨(x, false), hf, by simp⟩
    · exact hkeep E hE ht hf false
  · -- some positive clause fails without `x`: every negative clause holds without `x`
    push Not at hall
    obtain ⟨C, hCφ, hCt, hCf, hCrest⟩ := hall
    refine ⟨true, fun E hE ↦ ?_⟩
    by_cases ht : (x, true) ∈ E <;> by_cases hf : (x, false) ∈ E
    · exact htaut E ht hf _
    · exact ⟨(x, true), ht, by simp⟩
    · have hres := h _ (mem_eliminate.mpr (Or.inr ⟨C, hCφ, ⟨hCt, hCf⟩, E, hE, ⟨hf, ht⟩, rfl⟩))
      obtain ⟨l, hl, hls⟩ := hres
      rcases CNFClause.mem_resolvent.mp hl with ⟨hlC, hne⟩ | ⟨hlE, hne⟩
      · exact absurd ⟨l, List.mem_filter.mpr ⟨hlC, by simpa using hne⟩, hls⟩ hCrest
      · refine ⟨l, hlE, ?_⟩
        have hlx : l.1 ≠ x := fst_ne_of_mem_resolvent hCf ht hl
        simp only [CNFLiteral.satisfies_def, Function.update_of_ne hlx] at hls ⊢
        exact hls
    · exact hkeep E hE ht hf true

/-- **Davis-Putnam step**: eliminating a variable preserves satisfiability. -/
theorem cnfSat_eliminate_iff (x : Nat) (φ : CNF) : CNFSat (eliminate x φ) ↔ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies, cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨b, hb⟩ := exists_satisfies_update_of_satisfies_eliminate hσ
    exact ⟨_, hb⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, satisfies_eliminate hσ⟩

/-! ### The procedure -/

/-- Eliminate the variables of `xs`, first to last. -/
def eliminateAll : List Nat → CNF → CNF
  | [], φ => φ
  | x :: xs, φ => eliminateAll xs (eliminate x φ)

theorem cnfSat_eliminateAll_iff (xs : List Nat) (φ : CNF) :
    CNFSat (eliminateAll xs φ) ↔ CNFSat φ := by
  induction xs generalizing φ with
  | nil => rfl
  | cons x xs ih => rw [eliminateAll, ih, cnfSat_eliminate_iff]

theorem vars_eliminateAll_subset (xs : List Nat) (φ : CNF) :
    (eliminateAll xs φ).vars ⊆ φ.vars \ xs.toFinset := by
  induction xs generalizing φ with
  | nil => simp [eliminateAll]
  | cons x xs ih =>
    intro y hy
    have h1 := ih (eliminate x φ) hy
    rw [Finset.mem_sdiff] at h1
    have h2 := vars_eliminate_subset x φ h1.1
    rw [Finset.mem_erase] at h2
    simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
      not_or] at h1 ⊢
    exact ⟨h2.2, h2.1, h1.2⟩

/-- The variables of `φ` as a list without repetitions (`eraseDups` is quadratic in the number
of literal occurrences, which the eliminations dominate). -/
def varList (φ : CNF) : List Nat := (φ.flatMap (List.map Prod.fst)).eraseDups

theorem mem_varList {x : Nat} {φ : CNF} : x ∈ varList φ ↔ x ∈ φ.vars := by
  simp [varList, List.mem_eraseDups, mem_vars]

/-- The Davis-Putnam procedure: eliminate every variable, then check for the empty clause. -/
def davisPutnam (φ : CNF) : Bool := decide ([] ∉ eliminateAll (varList φ) φ)

/-- **Correctness of the Davis-Putnam procedure.** -/
theorem davisPutnam_eq_true_iff (φ : CNF) : davisPutnam φ = true ↔ CNFSat φ := by
  rw [davisPutnam, decide_eq_true_iff, ← cnfSat_eliminateAll_iff (varList φ) φ]
  have hvars : (eliminateAll (varList φ) φ).vars = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    have := vars_eliminateAll_subset (varList φ) φ hy
    simp only [Finset.mem_sdiff, List.mem_toFinset, mem_varList] at this
    exact this.2 this.1
  constructor
  · intro hnil
    by_contra hunsat
    exact hnil (nil_mem_of_vars_eq_empty hvars hunsat)
  · intro hsat hnil
    rw [cnfSat_iff_exists_satisfies] at hsat
    obtain ⟨σ, hσ⟩ := hsat
    simpa using hσ [] hnil

end CNF

end Cslib.Logic.PL
