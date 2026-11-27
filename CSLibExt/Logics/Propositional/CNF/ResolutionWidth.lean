/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.CNF.Resolution

/-!
# Size and width of resolution proofs

Proof objects for resolution with the weakening rule, in the two forms of Ben-Sasson and
Wigderson (*Short proofs are narrow — resolution made simple*, J. ACM 48 (2001), 149-169,
Section 2.1): tree-like derivations (`ResolutionTree`) and general derivations given as a
sequence of lines (`IsResolutionDerivation`), together with their size (number of lines) and
width (largest number of distinct literals in a line). Both are sound
(`ResolutionTree.not_cnfSat`, `not_cnfSat_of_isResolutionRefutation`). The size-width relations
of Ben-Sasson and Wigderson are recorded in
`WantedExt/TheoryOfComputation/BenSassonWigdersonWanted`.

Clauses are lists of literals, so the width of a clause counts its distinct literals.
-/

@[expose] public section

namespace Cslib.Logic.LegacyPL

namespace CNFClause

/-- **Width of a clause.** The number of distinct literals of the clause (Ben-Sasson and
Wigderson, J. ACM 48 (2001), Section 2.3). -/
def width (C : CNFClause) : ℕ := C.toFinset.card

end CNFClause

namespace CNF

/-- **Width of a CNF formula.** The largest width of one of its clauses, `0` for the empty
formula (Ben-Sasson and Wigderson, J. ACM 48 (2001), Section 2.3). -/
def maxClauseWidth (φ : CNF) : ℕ := (φ.map CNFClause.width).foldr max 0

/-- **Tree-like resolution derivation.** A tree-like derivation of the clause `C` from the
clauses of `φ`: a leaf is a clause of `φ`, an inner node applies the resolution rule (from
`E ∨ x` and `F ∨ ¬x` derive `E ∨ F`) or the weakening rule (from `E` derive any clause
containing all literals of `E`). Clauses of `φ` may be used at several leaves (Ben-Sasson and
Wigderson, J. ACM 48 (2001), Section 2.1). -/
inductive ResolutionTree (φ : CNF) : CNFClause → Type
  /-- A clause of the formula. -/
  | ax {C : CNFClause} : C ∈ φ → ResolutionTree φ C
  /-- Resolve a clause containing `(x, true)` with one containing `(x, false)`. -/
  | resolve {C D : CNFClause} (x : ℕ) : ResolutionTree φ C → ResolutionTree φ D →
      (x, true) ∈ C → (x, false) ∈ D → ResolutionTree φ (CNFClause.resolvent x C D)
  /-- Weaken a clause to one containing all of its literals. -/
  | weaken {C D : CNFClause} : ResolutionTree φ C → (∀ l ∈ C, l ∈ D) → ResolutionTree φ D

namespace ResolutionTree

variable {φ : CNF}

/-- **Size of a tree-like derivation.** The number of lines (nodes) of the tree. -/
def proofSize : {C : CNFClause} → ResolutionTree φ C → ℕ
  | _, ax _ => 1
  | _, resolve _ t u _ _ => t.proofSize + u.proofSize + 1
  | _, weaken t _ => t.proofSize + 1

/-- **Width of a tree-like derivation.** The largest width of a line of the tree. -/
def proofWidth : {C : CNFClause} → ResolutionTree φ C → ℕ
  | C, ax _ => C.width
  | _, @resolve _ C D x t u _ _ =>
    max (CNFClause.resolvent x C D).width (max t.proofWidth u.proofWidth)
  | C, weaken t _ => max C.width t.proofWidth

/-- **Soundness of tree-like resolution.** Every clause with a tree-like derivation from `φ`
holds under every assignment satisfying `φ`. -/
theorem satisfies {C : CNFClause} (t : ResolutionTree φ C) {assignment : Nat → Bool}
    (hφ : φ.Satisfies assignment) : C.Satisfies assignment := by
  induction t with
  | ax hC => exact hφ _ hC
  | resolve x _ _ _ _ ihC ihD => exact CNFClause.satisfies_resolvent ihC ihD
  | weaken _ hsub ih =>
    obtain ⟨l, hl, hsat⟩ := ih
    exact ⟨l, hsub l hl, hsat⟩

/-- **A tree-like refutation proves unsatisfiability.** A formula with a tree-like derivation of
the empty clause is unsatisfiable. -/
theorem not_cnfSat (t : ResolutionTree φ []) : ¬ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies]
  rintro ⟨assignment, hφ⟩
  simpa using t.satisfies hφ

end ResolutionTree

/-- **One step of a resolution derivation.** The clause `C` may follow the lines `earlier`
in a resolution derivation from `φ`: it is a clause of `φ`, the resolvent on some variable of
two earlier lines, or a weakening of an earlier line. -/
def IsResolutionStep (φ : CNF) (earlier : List CNFClause) (C : CNFClause) : Prop :=
  C ∈ φ ∨
    (∃ x : ℕ, ∃ D ∈ earlier, ∃ E ∈ earlier,
      (x, true) ∈ D ∧ (x, false) ∈ E ∧ C = CNFClause.resolvent x D E) ∨
    (∃ D ∈ earlier, ∀ l ∈ D, l ∈ C)

/-- **Resolution derivation.** A list `π` of clauses is a resolution derivation from `φ` when
every line is a clause of `φ` or follows from earlier lines by the resolution rule or the
weakening rule (Ben-Sasson and Wigderson, J. ACM 48 (2001), Section 2.1). Its size is the
length of `π`. -/
def IsResolutionDerivation (φ : CNF) (π : List CNFClause) : Prop :=
  ∀ i (h : i < π.length), IsResolutionStep φ (π.take i) π[i]

/-- **Resolution refutation.** A resolution derivation from `φ` whose last line is the empty
clause. -/
def IsResolutionRefutation (φ : CNF) (π : List CNFClause) : Prop :=
  IsResolutionDerivation φ π ∧ π.getLast? = some []

/-- **Width of a derivation.** The largest width of one of its lines. -/
def derivationWidth (π : List CNFClause) : ℕ := (π.map CNFClause.width).foldr max 0

/-- **Soundness of resolution derivations.** Every line of a resolution derivation from `φ`
holds under every assignment satisfying `φ`. -/
theorem IsResolutionDerivation.satisfies_of_mem {φ : CNF} {π : List CNFClause}
    (h : IsResolutionDerivation φ π) {assignment : Nat → Bool} (hφ : φ.Satisfies assignment) :
    ∀ C ∈ π, C.Satisfies assignment := by
  have key : ∀ i (hi : i < π.length), π[i].Satisfies assignment := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hearlier : ∀ D ∈ π.take i, D.Satisfies assignment := by
        intro D hD
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
        rw [List.length_take] at hj
        rw [List.getElem_take]
        exact ih j (lt_of_lt_of_le hj (min_le_left _ _)) _
      rcases h i hi with hax | ⟨x, D, hD, E, hE, hx, hx', heq⟩ | ⟨D, hD, hsub⟩
      · exact hφ _ hax
      · rw [heq]; exact CNFClause.satisfies_resolvent (hearlier D hD) (hearlier E hE)
      · obtain ⟨l, hl, hsat⟩ := hearlier D hD
        exact ⟨l, hsub l hl, hsat⟩
  intro C hC
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
  exact key i hi

/-- **A refutation proves unsatisfiability.** A formula with a resolution refutation is
unsatisfiable. -/
theorem not_cnfSat_of_isResolutionRefutation {φ : CNF} {π : List CNFClause}
    (h : IsResolutionRefutation φ π) : ¬ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies]
  rintro ⟨assignment, hφ⟩
  have hmem : [] ∈ π := List.mem_of_getLast? h.2
  simpa using h.1.satisfies_of_mem hφ [] hmem

end CNF

end Cslib.Logic.LegacyPL
