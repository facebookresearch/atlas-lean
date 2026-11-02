/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.Bounded
public import CSLibExt.AutomatedReasoning.StringConstraints.Complexity
public import CSLibExt.AutomatedReasoning.StringConstraints.Levi
public import CSLibExt.AutomatedReasoning.StringConstraints.StraightLine
public import CSLibExt.AutomatedReasoning.StringConstraints.Undecidable

/-!
# String-constraint tests: boundary checks

End-to-end exercises for the string-constraint formalization: Levi's
lemma, the bounded solver on a satisfiable and an unsatisfiable
formula, the straight-line fold on a two-definition system, the PCP
encoding on a two-domino instance, and the SAT encoding on a
one-clause formula. The bounded-solver checks go through
`boundedSatB_iff` (the solver is `noncomputable`, so they are not
evaluated by `decide`).
-/

@[expose] public section

namespace StringConstraintsTests

open Cslib.AutomatedReasoning.StringConstraints
open Cslib.Decidability
open Cslib.Logic.PL

/-- Levi's lemma: cancellation of a common prefix. -/
example {a b : List Bool} (h : [true] ++ a = [true] ++ b) : a = b :=
  append_left_cancel h

/-- The bounded solver reports a satisfiable equation. -/
example : boundedSatB [0]
    (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [true]))) 1 = true := by
  have hvars : ∀ i ∈ varsOfFormula
      (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [true]))), i ∈ [0] := by
    decide
  rw [boundedSatB_iff _ _ _ hvars]
  exact ⟨fun _ => [true], fun _ _ => by simp, by simp [SatAtom]⟩

/-- The bounded solver reports a contradictory pair of equations. -/
example : boundedSatB [0]
    (Formula.and (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [true])))
      (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [false])))) 1
    = false := by
  have hvars : ∀ i ∈ varsOfFormula
      (Formula.and (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [true])))
        (Formula.atom (Atom.eq (Term.var (0 : Fin 1)) (Term.const [false])))), i ∈ [0] := by
    decide
  rw [Bool.eq_false_iff]
  intro h
  rw [boundedSatB_iff _ _ _ hvars] at h
  obtain ⟨σ, -, hSat⟩ := h
  simp [sat_and, SatAtom] at hSat
  simp [hSat.1] at hSat

/-- A two-definition straight-line system. -/
def twoDefSys : SLSys Bool where
  defs := [Term.const [true],
    Term.append (Term.var 0) (Term.const [false])]
  query := Formula.atom (Atom.eq (Term.var 1) (Term.const [true, false]))

/-- The two-definition system is acyclic. -/
theorem twoDefSys_acyclic : Acyclic twoDefSys := by
  constructor
  · intro k hk j hj
    have hlen : twoDefSys.defs.length = 2 := rfl
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp [twoDefSys] at hj
    · simp [twoDefSys, varsOf] at hj
      omega
  · intro j hj
    have hlen : twoDefSys.defs.length = 2 := rfl
    simp [twoDefSys, varsOfFormula, varsOfAtom] at hj
    omega

/-- The straight-line system is satisfiable, with value `[true, false]`
at variable `1`. -/
example : ∃ σ, SLSat twoDefSys σ := by
  refine ⟨sol twoDefSys, ?_, ?_⟩
  · intro k hk
    exact sol_satisfies_defs twoDefSys twoDefSys_acyclic k hk
  · exact (by decide : sol twoDefSys 1 = [true, false])

/-- A two-domino PCP instance with solution `[d₁, d₂]`. -/
def twoDomino : List (Post.Domino Bool) :=
  [([true], [true, true]), ([true, true], [true])]

/-- The two-domino instance is a PCP instance. -/
theorem twoDomino_pcp : Post.PCP twoDomino :=
  ⟨twoDomino, by decide, by decide, by decide⟩

/-- The PCP encoding of the two-domino instance is satisfiable. -/
example : ∃ σ, Sat σ (pcpConstraint twoDomino) :=
  (pcp_iff_stringSat twoDomino).mp twoDomino_pcp

/-- A one-clause CNF formula is satisfiable. -/
theorem oneClause_sat : CNFSat ([[(0, true)]] : CNF) := by
  refine ⟨fun _ => true, fun C hC => ?_⟩
  simp at hC
  subst hC
  exact ⟨0, true, by simp, rfl⟩

/-- The SAT encoding of the one-clause formula is satisfiable. -/
example : ∃ σ : ℕ → List Bool, (∀ i, (σ i).length ≤ 1) ∧
    Sat σ (encodeCNF ([[(0, true)]] : CNF)) :=
  (cnfSat_iff_stringSat _).mp oneClause_sat

/-- Levi's lemma on a concrete split: the second disjunct holds with `w = [2]`. -/
example : (∃ w : List ℕ, [1] = [1, 2] ++ w ∧ [3] = w ++ [2, 3]) ∨
    (∃ w : List ℕ, [1, 2] = [1] ++ w ∧ [2, 3] = w ++ [3]) :=
  levi (by rfl)

/-- A `mem` atom: `[true]` belongs to the regex `char true`. -/
example : Sat (fun _ : Fin 1 => [true])
    (Formula.atom (Atom.mem (Term.var 0)
      (Cslib.Language.EncodedRegex.flatten (RegularExpression.char true)))) := by
  change [true] ∈ (Cslib.Language.EncodedRegex.flatten
    (RegularExpression.char true)).toRegex.matches'
  rw [Cslib.Language.EncodedRegex.toRegex_flatten,
    RegularExpression.matches'_char]
  exact Set.mem_singleton _

/-- Length atoms: `[true]` satisfies `|x| ≤ 1` and `1 ≤ |x|`. -/
example : Sat (fun _ : Fin 1 => [true])
    (Formula.and (Formula.atom (Atom.lenLe (Term.var 0) 1))
      (Formula.atom (Atom.lenGe (Term.var 0) 1))) := by
  simp [Sat, SatAtom, eval]

/-- A `hom` atom: mapping `[true]` through `fun _ => [true, false]`. -/
example : Sat (fun _ : Fin 1 => [true])
    (Formula.atom (Atom.eq (Term.hom (fun _ => [true, false]) (Term.var 0))
      (Term.const [true, false]))) := by
  simp [Sat, SatAtom, eval]

/-- An unsatisfiable straight-line system: `x₀ = [true]` but the query
demands `x₀ = [false]`. -/
def unsatSys : SLSys Bool where
  defs := [Term.const [true]]
  query := Formula.atom (Atom.eq (Term.var 0) (Term.const [false]))

theorem unsatSys_acyclic : Acyclic unsatSys := by
  constructor
  · intro k hk j hj
    have hlen : unsatSys.defs.length = 1 := rfl
    rcases (by omega : k = 0) with rfl
    simp [unsatSys] at hj
  · intro j hj
    have hlen : unsatSys.defs.length = 1 := rfl
    simp [unsatSys, varsOfFormula, varsOfAtom] at hj
    omega

/-- The unsatisfiable straight-line system has no satisfying assignment. -/
example : ¬ ∃ σ, SLSat unsatSys σ := by
  intro h
  have h2 := (exists_sat_iff_sat_sol unsatSys unsatSys_acyclic).mp h
  change eval (sol unsatSys) (Term.var 0) = eval (sol unsatSys) (Term.const [false]) at h2
  simp only [eval] at h2
  have h3 : sol unsatSys 0 = [true] := by decide
  rw [h3] at h2
  exact (by decide : ([true] : List Bool) ≠ [false]) h2

/-- The two contradictory unit clauses are unsatisfiable. -/
theorem twoClause_unsat : ¬ CNFSat ([[(0, true)], [(0, false)]] : CNF) := by
  rintro ⟨v, hv⟩
  have h1 := hv [(0, true)] (by simp)
  have h2 := hv [(0, false)] (by simp)
  obtain ⟨x, b, hx, hvx⟩ := h1
  obtain ⟨x', b', hx', hvx'⟩ := h2
  simp only [List.mem_singleton, Prod.mk.injEq] at hx hx'
  obtain ⟨rfl, rfl⟩ : x = 0 ∧ b = true := hx
  obtain ⟨rfl, rfl⟩ : x' = 0 ∧ b' = false := hx'
  rw [hvx] at hvx'
  simp at hvx'

/-- The bounded solver rejects the encoding of the contradiction. -/
example : boundedSatB [0]
    (encodeCNF ([[(0, true)], [(0, false)]] : CNF)) 1 = false := by
  rw [Bool.eq_false_iff, ne_eq,
    ← cnfSat_iff_boundedSatB ([[(0, true)], [(0, false)]] : CNF) [0] (by decide)]
  exact twoClause_unsat

end StringConstraintsTests
