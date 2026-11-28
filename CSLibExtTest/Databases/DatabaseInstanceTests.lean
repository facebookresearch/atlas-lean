/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.DatabaseInstance
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Tests for database instances

Attributes are `0, 1, 2, 3 : Fin 4` (think `A`, `B`, `C`, `E`); values are natural numbers.
* The three-relation instance `I` over `R(A, B)`, `S(B, C)` and `T(C, E)`.
* Typing soundness on `I`, query-level associativity, the active domain, and the six query
  rewrites, each applied on this schema.
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

/-- Selecting on a literal absent from the instance: the result, and so its active domain, is
empty. The constant `10` does not leak into the output. -/
example : adom ((Expr.select (.eqConst 1 10) (.rel 1) :
    Expr (Fin 3) (Fin 4) ℕ).eval I.rel) = ∅ := by
  decide

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

end Cslib.Databases.DatabaseInstanceTests
