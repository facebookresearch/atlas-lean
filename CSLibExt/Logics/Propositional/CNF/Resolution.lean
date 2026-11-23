/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Resolution for conjunctive normal form
-/
module

public import CSLibExt.Logics.Propositional.CNF.Restriction

/-!
# Resolution for conjunctive normal form

Resolution derives clauses from a CNF formula with one rule: from a clause
containing the literal `(x, true)` and a clause containing `(x, false)`, derive
their resolvent, the union of the two clauses with every occurrence of those
two literals removed.  A *resolution refutation* of a formula is a derivation
of the empty clause.

This file proves that resolution is sound (every derived clause holds under
every satisfying assignment, so a refutable formula is unsatisfiable) and
refutation complete (every unsatisfiable formula has a refutation).

The completeness proof is by induction on the number of variables, through
the restriction `CNF.restrict` already used by the DPLL solver.  A refutation
of `φ` restricted by the literal `(x, b)` lifts to a derivation from `φ` of a
clause whose literals are those of the restricted clause plus possibly
`(x, !b)`.  The two lifted refutations, one per value of `x`, resolve on `x`
to the empty clause.

## Main definitions

- `CNFClause.resolvent x C D` : `C` without `(x, true)`, followed by `D`
  without `(x, false)`.
- `CNF.ResolutionDerivable φ C` : `C` is derivable from the clauses of `φ`
  by resolution.

## Main results

- `CNF.ResolutionDerivable.satisfies` : soundness for derived clauses.
- `CNF.not_cnfSat_of_resolutionDerivable_nil` : a refutable formula is
  unsatisfiable.
- `CNF.resolutionDerivable_nil_of_not_cnfSat` : refutation completeness.
- `CNF.resolutionDerivable_nil_iff_not_cnfSat` : both together.

## References

- J. A. Robinson, *A machine-oriented logic based on the resolution principle*,
  J. ACM 12(1), 1965, 23-41.
- U. Schöning, *Logic for Computer Scientists*, Birkhäuser 1989, §1.5
  (resolution soundness and completeness).
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace CNFClause

/-- **Resolvent of two clauses.** Let $x$ be a variable and $C$, $D$ clauses. The resolvent of $C$
and $D$ on $x$ is the clause consisting of the literals of $C$ other than $(x, \mathrm{true})$,
in order, followed by the literals of $D$ other than $(x, \mathrm{false})$, in order. -/
def resolvent (x : Nat) (C D : CNFClause) : CNFClause :=
  C.filter (· ≠ (x, true)) ++ D.filter (· ≠ (x, false))

@[simp]
theorem mem_resolvent {x : Nat} {C D : CNFClause} {literal : Nat × Bool} :
    literal ∈ resolvent x C D ↔
      (literal ∈ C ∧ literal ≠ (x, true)) ∨ (literal ∈ D ∧ literal ≠ (x, false)) := by
  simp [resolvent]

/-- **Resolution rule soundness.** Let $x$ be a variable and $C$, $D$ clauses. Every assignment
that satisfies both $C$ and $D$ satisfies the resolvent of $C$ and $D$ on $x$. -/
theorem satisfies_resolvent {assignment : Nat → Bool} {x : Nat} {C D : CNFClause}
    (hC : C.Satisfies assignment) (hD : D.Satisfies assignment) :
    (resolvent x C D).Satisfies assignment := by
  obtain ⟨l, hl, hlsat⟩ := hC
  obtain ⟨m, hm, hmsat⟩ := hD
  by_cases hlx : l = (x, true)
  · by_cases hmx : m = (x, false)
    · subst hlx hmx
      simp only [CNFLiteral.satisfies_def] at hlsat hmsat
      rw [hlsat] at hmsat
      exact absurd hmsat (by decide)
    · exact ⟨m, mem_resolvent.mpr (Or.inr ⟨hm, hmx⟩), hmsat⟩
  · exact ⟨l, mem_resolvent.mpr (Or.inl ⟨hl, hlx⟩), hlsat⟩

end CNFClause

namespace CNF

/-- **Resolution derivability.** Given a CNF formula $\varphi$, the clauses derivable from
$\varphi$ by resolution form the smallest set $S$ of clauses that contains every clause of
$\varphi$ and, for every variable $x$ and all clauses $C, D \in S$ such that $C$ contains the
literal $(x, \mathrm{true})$ and $D$ contains the literal $(x, \mathrm{false})$, contains the
resolvent of $C$ and $D$ on $x$. -/
inductive ResolutionDerivable (φ : CNF) : CNFClause → Prop
  /-- Every clause of the formula is derivable. -/
  | ax {C : CNFClause} : C ∈ φ → ResolutionDerivable φ C
  /-- Resolve a clause containing `(x, true)` with one containing `(x, false)`. -/
  | resolve {C D : CNFClause} (x : Nat) :
      ResolutionDerivable φ C → ResolutionDerivable φ D → (x, true) ∈ C → (x, false) ∈ D →
      ResolutionDerivable φ (CNFClause.resolvent x C D)

/-! ### Soundness -/

/-- **Soundness of resolution.** Let $\varphi$ be a CNF formula. Every clause derivable by
resolution from $\varphi$ is satisfied by every assignment that satisfies $\varphi$. -/
theorem ResolutionDerivable.satisfies {φ : CNF} {C : CNFClause} {assignment : Nat → Bool}
    (h : φ.ResolutionDerivable C) (hφ : φ.Satisfies assignment) : C.Satisfies assignment := by
  induction h with
  | ax hC => exact hφ _ hC
  | resolve x _ _ _ _ ihC ihD => exact CNFClause.satisfies_resolvent ihC ihD

/-- **Refutable formulas are unsatisfiable.** If the empty clause is derivable by resolution
from a CNF formula $\varphi$, then $\varphi$ is not satisfiable. -/
theorem not_cnfSat_of_resolutionDerivable_nil {φ : CNF} (h : φ.ResolutionDerivable []) :
    ¬ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies]
  rintro ⟨assignment, hφ⟩
  simpa using h.satisfies hφ

/-! ### Completeness -/

/-- **Clauses of a restricted formula.** Let $\varphi$ be a CNF formula and $\ell$ a literal. A
clause $C$ belongs to the restriction of $\varphi$ by $\ell$ if and only if there is a clause $C_0$
of $\varphi$ that does not contain $\ell$ such that $C$ is the restriction of $C_0$ by $\ell$. -/
theorem mem_restrict_iff {literal : Nat × Bool} {φ : CNF} {C : CNFClause} :
    C ∈ φ.restrict literal ↔ ∃ C₀ ∈ φ, literal ∉ C₀ ∧ C = C₀.restrict literal := by
  induction φ with
  | nil => simp
  | cons clause φ ih =>
    rw [restrict_cons]
    split
    next hmem =>
      rw [ih]
      constructor
      · rintro ⟨C₀, hC₀, hnot, rfl⟩
        exact ⟨C₀, List.mem_cons_of_mem _ hC₀, hnot, rfl⟩
      · rintro ⟨C₀, hC₀, hnot, rfl⟩
        rcases List.mem_cons.mp hC₀ with rfl | hC₀
        · exact absurd hmem hnot
        · exact ⟨C₀, hC₀, hnot, rfl⟩
    next hmem =>
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨C₀, hC₀, hnot, rfl⟩)
        · exact ⟨clause, List.mem_cons_self .., hmem, rfl⟩
        · exact ⟨C₀, List.mem_cons_of_mem _ hC₀, hnot, rfl⟩
      · rintro ⟨C₀, hC₀, hnot, rfl⟩
        rcases List.mem_cons.mp hC₀ with rfl | hC₀
        · exact Or.inl rfl
        · exact Or.inr ⟨C₀, hC₀, hnot, rfl⟩

/-- **Lifting lemma.** Let $\varphi$ be a CNF formula, $x$ a variable and $b$ a Boolean value. If a
clause $D$ is derivable by resolution from the restriction of $\varphi$ by the literal $(x, b)$,
then some clause $D_0$ is derivable by resolution from $\varphi$ such that every literal of $D_0$
is either a literal of $D$ or the complementary literal $(x, \lnot b)$. -/
theorem ResolutionDerivable.lift_restrict {φ : CNF} {x : Nat} {b : Bool} {D : CNFClause}
    (h : (φ.restrict (x, b)).ResolutionDerivable D) :
    ∃ D₀, φ.ResolutionDerivable D₀ ∧ ∀ l ∈ D₀, l ∈ D ∨ l = (x, !b) := by
  induction h with
  | @ax D hD =>
    obtain ⟨C₀, hC₀, hnot, rfl⟩ := mem_restrict_iff.mp hD
    refine ⟨C₀, .ax hC₀, fun l hl ↦ ?_⟩
    by_cases hlx : l.1 = x
    · right
      obtain ⟨y, c⟩ := l
      simp only at hlx
      subst hlx
      have hc : c ≠ b := fun hcb ↦ hnot (hcb ▸ hl)
      cases b <;> cases c <;> simp_all
    · exact Or.inl (CNFClause.mem_restrict.mpr ⟨hl, hlx⟩)
  | @resolve D₁ D₂ y _ _ h₁ h₂ ih₁ ih₂ =>
    obtain ⟨E₁, hE₁, hsub₁⟩ := ih₁
    obtain ⟨E₂, hE₂, hsub₂⟩ := ih₂
    by_cases hy₁ : (y, true) ∈ E₁
    · by_cases hy₂ : (y, false) ∈ E₂
      · refine ⟨CNFClause.resolvent y E₁ E₂, .resolve y hE₁ hE₂ hy₁ hy₂, fun l hl ↦ ?_⟩
        rcases CNFClause.mem_resolvent.mp hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
        · exact (hsub₁ l hl).imp_left fun hD ↦ CNFClause.mem_resolvent.mpr (Or.inl ⟨hD, hne⟩)
        · exact (hsub₂ l hl).imp_left fun hD ↦ CNFClause.mem_resolvent.mpr (Or.inr ⟨hD, hne⟩)
      · refine ⟨E₂, hE₂, fun l hl ↦ ?_⟩
        have hne : l ≠ (y, false) := fun h ↦ hy₂ (h ▸ hl)
        exact (hsub₂ l hl).imp_left fun hD ↦ CNFClause.mem_resolvent.mpr (Or.inr ⟨hD, hne⟩)
    · refine ⟨E₁, hE₁, fun l hl ↦ ?_⟩
      have hne : l ≠ (y, true) := fun h ↦ hy₁ (h ▸ hl)
      exact (hsub₁ l hl).imp_left fun hD ↦ CNFClause.mem_resolvent.mpr (Or.inl ⟨hD, hne⟩)

/-- **Unsatisfiable formulas without variables contain the empty clause.** If a CNF formula
$\varphi$ has no variables and is not satisfiable, then the empty clause is one of the clauses
of $\varphi$. -/
theorem nil_mem_of_vars_eq_empty {φ : CNF} (hvars : φ.vars = ∅) (hφ : ¬ CNFSat φ) :
    [] ∈ φ := by
  by_contra hnil
  apply hφ
  refine ⟨fun _ ↦ false, fun C hC ↦ ?_⟩
  match C, hC with
  | [], hC => exact absurd hC hnil
  | (y, c) :: _, hC =>
    have : y ∈ φ.vars := mem_vars.mpr ⟨_, hC, c, List.mem_cons_self ..⟩
    simp [hvars] at this

/-- **Refutation completeness** of resolution: every unsatisfiable CNF formula has a
resolution derivation of the empty clause. -/
theorem resolutionDerivable_nil_of_not_cnfSat {φ : CNF} (hφ : ¬ CNFSat φ) :
    φ.ResolutionDerivable [] := by
  induction hn : φ.vars.card using Nat.strong_induction_on generalizing φ with
  | _ n ih =>
  subst hn
  rcases Finset.eq_empty_or_nonempty φ.vars with hvars | ⟨x, hx⟩
  · exact .ax (nil_mem_of_vars_eq_empty hvars hφ)
  · rw [sat_iff_restrict_true_or_false φ x, not_or] at hφ
    obtain ⟨E₁, hE₁, hsub₁⟩ :=
      (ih _ (card_vars_restrict_lt (literal := (x, true)) hx) hφ.1 rfl).lift_restrict
    obtain ⟨E₂, hE₂, hsub₂⟩ :=
      (ih _ (card_vars_restrict_lt (literal := (x, false)) hx) hφ.2 rfl).lift_restrict
    simp only [List.not_mem_nil, false_or, Bool.not_true, Bool.not_false] at hsub₁ hsub₂
    by_cases h₁ : (x, false) ∈ E₁
    · by_cases h₂ : (x, true) ∈ E₂
      · convert ResolutionDerivable.resolve x hE₂ hE₁ h₂ h₁
        symm
        rw [List.eq_nil_iff_forall_not_mem]
        intro l hl
        rcases CNFClause.mem_resolvent.mp hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
        · exact hne (hsub₂ l hl)
        · exact hne (hsub₁ l hl)
      · rw [List.eq_nil_iff_forall_not_mem.mpr fun l hl ↦ h₂ (hsub₂ l hl ▸ hl)] at hE₂
        exact hE₂
    · rw [List.eq_nil_iff_forall_not_mem.mpr fun l hl ↦ h₁ (hsub₁ l hl ▸ hl)] at hE₁
      exact hE₁

/-- **Soundness and refutation completeness**: a CNF formula has a resolution refutation
iff it is unsatisfiable. -/
theorem resolutionDerivable_nil_iff_not_cnfSat {φ : CNF} :
    φ.ResolutionDerivable [] ↔ ¬ CNFSat φ :=
  ⟨not_cnfSat_of_resolutionDerivable_nil, resolutionDerivable_nil_of_not_cnfSat⟩

end CNF

end Cslib.Logic.PL
