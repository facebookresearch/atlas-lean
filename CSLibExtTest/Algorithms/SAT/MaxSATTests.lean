/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.SAT.MaxSAT.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for the MAX-SAT bounds

Each public bound is applied to a concrete formula with its hypotheses
discharged there. The single-clause instances force a satisfying assignment;
the repeated-clause instances show that occurrences are counted: as a finset
the formula `x₀, x₀, ¬x₀` collapses to two clauses, while as a canonical CNF
formula the one-half bound needs two satisfied positions and so forces
`x₀ = true`.
-/

namespace CSLibExtTest.Algorithms.SAT.MaxSAT

open Cslib.Logic.PL Cslib.Algorithms.SAT.MaxSAT

/-- The clause `x₀ ∨ x₁ ∨ ¬x₂` over three variables. -/
def c₀ : Finset (Lit 3) := {(0, true), (1, true), (2, false)}

/-- `c₀` has three literals on three distinct variables. -/
theorem c₀_three :
    c₀.card = 3 ∧ Set.InjOn (fun l : Lit 3 => l.1) (c₀ : Set (Lit 3)) := by
  refine ⟨by decide, ?_⟩
  intro a ha b hb hab
  simp only [c₀, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all

/-- The duplicate-free 7/8 bound applied to the one-clause formula `{c₀}`:
since `7 / 8 * 1` exceeds `0`, the assignment it provides satisfies `c₀`. -/
example : ∃ x : Fin 3 → Bool, clauseSat x c₀ := by
  obtain ⟨x, hx⟩ := max_e3sat_seven_eighths_finset {c₀} (fun c hc => by
    rw [Finset.mem_singleton] at hc
    exact hc ▸ c₀_three)
  refine ⟨x, ?_⟩
  by_contra h
  norm_num [Finset.filter_singleton, h] at hx

/-- The indexed 7/8 bound counts a repeated clause once per index: on the
family `c₀, c₀` it gives `7 / 8 * 2 ≤` the number of satisfied indices. -/
example : ∃ x : Fin 3 → Bool, (7 / 8 : ℝ) * (Finset.univ : Finset (Fin 2)).card ≤
    ((Finset.univ.filter
      (fun i : Fin 2 => clauseSat x ((![c₀, c₀] : Fin 2 → Finset (Lit 3)) i))).card :
        ℝ) :=
  max_e3sat_seven_eighths _ _ (fun i _ => by fin_cases i <;> exact c₀_three)

/-- The literal clause `x₀`. -/
def pos₀ : Finset (Lit 1) := {(0, true)}

/-- The literal clause `¬x₀`. -/
def neg₀ : Finset (Lit 1) := {(0, false)}

/-- As a finset, the formula `x₀, x₀, ¬x₀` has only two clauses. -/
example : ({pos₀, pos₀, neg₀} : Finset (Finset (Lit 1))).card = 2 := by
  decide

/-- The duplicate-free one-half bound on `{x₀, ¬x₀}`. -/
example : ∃ x : Fin 1 → Bool,
    (1 / 2 : ℝ) * ({pos₀, neg₀} : Finset (Finset (Lit 1))).card ≤
      (({pos₀, neg₀} : Finset (Finset (Lit 1))).filter
        (fun c => clauseSat x c)).card :=
  max_sat_half_finset _ (fun c hc => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl <;> decide)

/-- The indexed one-half bound on the family `x₀, x₀, ¬x₀`. -/
example : ∃ x : Fin 1 → Bool, (1 / 2 : ℝ) * (Finset.univ : Finset (Fin 3)).card ≤
    ((Finset.univ.filter
      (fun i : Fin 3 =>
        clauseSat x ((![pos₀, pos₀, neg₀] : Fin 3 → Finset (Lit 1)) i))).card : ℝ) :=
  max_sat_half _ _ (fun i _ => by fin_cases i <;> decide)

/-- The canonical CNF formula `x₀, x₀, ¬x₀`. -/
def ψ₀ : CNF := [[(0, true)], [(0, true)], [(0, false)]]

open Classical in
/-- The canonical one-half bound on `x₀, x₀, ¬x₀` counts positions, so it
needs two satisfied clauses and forces `x₀ = true`. -/
example : ∃ v : ℕ → Bool, v 0 = true := by
  obtain ⟨v, hv⟩ := cnf_max_sat_half ψ₀ (by decide)
  refine ⟨v, ?_⟩
  by_contra h
  have hsub : (Finset.univ : Finset (Fin ψ₀.length)).filter
      (fun i => CNFClause.Satisfies v ψ₀[i]) ⊆ {⟨2, by decide⟩} := by
    rintro ⟨k, hk⟩ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hk3 : k < 3 := by simpa [ψ₀] using hk
    interval_cases k
    · simp [ψ₀, h] at hi
    · simp [ψ₀, h] at hi
    · simp
  have hcard : (((Finset.univ : Finset (Fin ψ₀.length)).filter
      (fun i => CNFClause.Satisfies v ψ₀[i])).card : ℝ) ≤ 1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_singleton _).le
  have hlen : (ψ₀.length : ℝ) = 3 := by simp [ψ₀]
  rw [hlen] at hv
  linarith

/-- The canonical CNF formula `x₀ ∨ x₁ ∨ ¬x₂`, twice, and `¬x₀ ∨ ¬x₁ ∨ x₂`. -/
def φ₀ : CNF :=
  [[(0, true), (1, true), (2, false)], [(0, true), (1, true), (2, false)],
    [(0, false), (1, false), (2, true)]]

open Classical in
/-- The canonical 7/8 bound on `φ₀`, with its hypothesis decided on the
concrete clauses. -/
example : ∃ v : ℕ → Bool, (7 / 8 : ℝ) * φ₀.length ≤
    (((Finset.univ : Finset (Fin φ₀.length)).filter
      (fun i => CNFClause.Satisfies v φ₀[i])).card : ℝ) :=
  cnf_max_e3sat_seven_eighths φ₀ (by decide)

end CSLibExtTest.Algorithms.SAT.MaxSAT
