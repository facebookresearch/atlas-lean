/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.DatabaseInstance
public import CSLibExt.Databases.FunctionalDependencies
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Tests for database instances

Attributes are `0, 1, 2, 3 : Fin 4` (think `A`, `B`, `C`, `E`); values are natural numbers.
* The three-relation instance `I` over `R(A, B)`, `S(B, C)` and `T(C, E)`.
* Join associativity and selection pushdown, both by the theorems and by evaluation; pushing a
  condition on `E` into `R` changes the result, so the side condition is needed.
* Typing soundness on `I`, query-level associativity, the active domain, and the six query
  rewrites, each applied on this schema.
* The FD interface: `B → C` holds in `S`, while `A → B` fails in `R` extended by `⟨1, 3⟩`.
-/

@[expose] public section

namespace Cslib.Databases.DatabaseInstanceTests

open Cslib.Databases

/-- Attributes `0, 1, 2, 3 : Fin 4` (think `A, B, C, E`); values are natural numbers. -/
def tup (a b c e : Option ℕ) : Tuple (Fin 4) ℕ := ![a, b, c, e]

/-- `R(A, B)`. -/
def R : Finset (Tuple (Fin 4) ℕ) :=
  {tup (some 1) (some 2) none none, tup (some 2) (some 3) none none}

/-- `S(B, C)`. -/
def S : Finset (Tuple (Fin 4) ℕ) :=
  {tup none (some 2) (some 5) none, tup none (some 3) (some 6) none,
    tup none (some 4) (some 9) none}

/-- `T(C, E)`. -/
def T : Finset (Tuple (Fin 4) ℕ) :=
  {tup none none (some 5) (some 7), tup none none (some 6) (some 8),
    tup none none (some 0) (some 0)}

/-- The database schema: names `0, 1, 2` are `R(A, B)`, `S(B, C)`, `T(C, E)`. -/
def sch : Fin 3 → Finset (Fin 4) := ![{0, 1}, {1, 2}, {2, 3}]

theorem R_isOver : IsOver {0, 1} R := by
  unfold IsOver Tuple.IsOver
  decide

theorem S_isOver : IsOver {1, 2} S := by
  unfold IsOver Tuple.IsOver
  decide

theorem T_isOver : IsOver {2, 3} T := by
  unfold IsOver Tuple.IsOver
  decide

/-- The three-relation database instance. -/
def I : DatabaseInstance ℕ sch := ⟨![R, S, T], by
  intro n
  fin_cases n
  exacts [R_isOver, S_isOver, T_isOver]⟩

/-- Join associativity by the theorem `join_assoc` ... -/
example : join (join R S) T = join R (join S T) := join_assoc _ _ _

/-- ... and by evaluation, with the expected value. -/
example : join (join R S) T = join R (join S T) ∧
    join R (join S T) =
      {tup (some 1) (some 2) (some 5) (some 7), tup (some 2) (some 3) (some 6) (some 8)} := by
  decide

/-- Selection pushdown on `A = 1` by the theorem `select_join_left` (apply it with `R_isOver`). -/
example : select (.eqConst 0 1) (join R (join S T)) =
    join (select (.eqConst 0 1) R) (join S T) := by
  exact select_join_left _ _ R_isOver (by decide)

/-- ... and by evaluation. -/
example : select (.eqConst 0 1) (join R (join S T)) =
    {tup (some 1) (some 2) (some 5) (some 7)} := by
  decide

/-- Boundary: a condition on `E`, which `R` lacks, cannot be pushed into `R`. -/
example : select (.eqConst 3 7) (join R (join S T)) ≠
    join (select (.eqConst 3 7) R) (join S T) := by
  decide

/-- The adapter: the three-way join query type-checks with schema `{A, B, C, E}`, so by
`DatabaseInstance.eval_isOver` its value on `I` is a relation over that schema. -/
example : IsOver {0, 1, 2, 3}
    ((Expr.join (.join (.rel 0) (.rel 1)) (.rel 2) : Expr (Fin 3) (Fin 4) ℕ).eval I.rel) := by
  exact DatabaseInstance.eval_isOver I (by decide)

/-- Query-level join associativity on this schema (apply `Expr.join_assoc`). -/
example : Expr.Equiv sch (.join (.join (.rel 0) (.rel 1)) (.rel 2))
    (.join (.rel 0) (.join (.rel 1) (.rel 2)) : Expr (Fin 3) (Fin 4) ℕ) := by
  exact Expr.join_assoc rfl rfl rfl

/-- The active domain of `I`, by evaluation. -/
example : I.adom = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
  decide

/-- `mem_adom`, both directions on concrete values. -/
example : (9 : ℕ) ∈ I.adom ∧ (10 : ℕ) ∉ I.adom := by
  constructor
  · refine DatabaseInstance.mem_adom.mpr
      ⟨1, tup none (some 4) (some 9) none, by decide, 2, by decide⟩
  · intro h
    have hnone : ¬ ∃ n, ∃ t ∈ I.rel n, ∃ a, t a = some (10 : ℕ) := by decide
    exact hnone (DatabaseInstance.mem_adom.mp h)

/-- `adom_eval_subset` applied to a query (apply the theorem, not `decide`). -/
example : adom ((Expr.project {0, 3} (.join (.rel 0) (.join (.rel 1) (.rel 2))) :
    Expr (Fin 3) (Fin 4) ℕ).eval I.rel) ⊆ I.adom := by
  exact DatabaseInstance.adom_eval_subset I _

/-- Each new query rewrite applies on this schema (apply the named theorem). -/
example : Expr.Equiv sch
    (.select (.eqConst 1 2) (.union (.rel 1) (.project {1, 2} (.join (.rel 1) (.rel 2)))))
    (.union (.select (.eqConst 1 2) (.rel 1))
      (.select (.eqConst 1 2) (.project {1, 2} (.join (.rel 1) (.rel 2)))) :
      Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.select_union
  exact Expr.select_union (S := {1, 2}) (by decide) (by decide) (by decide)

example : Expr.Equiv sch
    (.select (.eqConst 1 2) (.diff (.rel 1) (.project {1, 2} (.join (.rel 1) (.rel 2)))))
    (.diff (.select (.eqConst 1 2) (.rel 1))
      (.select (.eqConst 1 2) (.project {1, 2} (.join (.rel 1) (.rel 2)))) :
      Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.select_diff
  exact Expr.select_diff (S := {1, 2}) (by decide) (by decide) (by decide)

example : Expr.Equiv sch
    (.project {1} (.union (.rel 1) (.project {1, 2} (.join (.rel 1) (.rel 2)))))
    (.union (.project {1} (.rel 1)) (.project {1} (.project {1, 2} (.join (.rel 1) (.rel 2)))) :
      Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.project_union
  exact Expr.project_union (S := {1, 2}) (by decide) (by decide) (by decide)

example : Expr.Equiv sch (.select (.eqConst 0 1) (.select (.eqAttr 1 1) (.rel 0)))
    (.select (.eqAttr 1 1) (.select (.eqConst 0 1) (.rel 0)) : Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.select_comm
  exact Expr.select_comm (S := {0, 1}) (by decide) (by decide) (by decide)

example : Expr.Equiv sch (.select (.eqConst 1 2) (.project {1} (.rel 0)))
    (.project {1} (.select (.eqConst 1 2) (.rel 0)) : Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.select_project
  exact Expr.select_project (S := {0, 1}) (by decide) (by decide) (by decide)

example : Expr.Equiv sch (.select (.eqConst 3 7) (.join (.rel 1) (.rel 2)))
    (.join (.rel 1) (.select (.eqConst 3 7) (.rel 2)) : Expr (Fin 3) (Fin 4) ℕ) := by
  -- Expr.select_join_right
  exact Expr.select_join_right (S := {1, 2}) (S' := {2, 3}) (by decide) (by decide) _ (by decide)

/-- FD interface: FD satisfaction on an RA relation is `FD.HoldsIn` at value type `Option D`,
definitionally; no tuple-type bijection is involved. -/
example {A D : Type*} (r : Finset (Tuple A D)) (f : FD A) :
    f.HoldsIn (↑r : Set (A → Option D)) ↔
      ∀ t ∈ r, ∀ u ∈ r, (∀ a ∈ f.lhs, t a = u a) → ∀ a ∈ f.rhs, t a = u a :=
  Iff.rfl

/-- A holding dependency: `B → C` holds in `S`. -/
example : FD.HoldsIn ⟨{1}, {2}⟩ (↑S : Set (Fin 4 → Option ℕ)) := by
  intro t ht u hu h
  simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ht hu
  rcases ht with rfl | rfl | rfl
  all_goals rcases hu with rfl | rfl | rfl
  all_goals revert h
  all_goals decide

/-- A failing dependency: in `R ∪ R'` with `R' = {⟨A:1, B:3⟩}`, `A → B` does not hold. -/
example : ¬ FD.HoldsIn ⟨{0}, {1}⟩
    (↑(R ∪ {tup (some 1) (some 3) none none}) : Set (Fin 4 → Option ℕ)) := by
  intro h
  have h2 :=
    h (tup (some 1) (some 2) none none) (by decide)
      (tup (some 1) (some 3) none none) (by decide) (by decide) 1 (by decide)
  revert h2
  decide

end Cslib.Databases.DatabaseInstanceTests
