/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.ActiveDomain
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Tests for active domains

Attributes are `0, 1, 2, 3 : Fin 4` (think `A`, `B`, `C`, `E`); values are natural numbers.
- The three-relation database `db` over `R(A, B)`, `S(B, C)` and `T(C, E)`, and the proof that
it conforms to its schema.
- Typing soundness on `db` through the landed `Expr.eval_isOver`, the active domain of `db` by
evaluation, `mem_adomDB` in both directions, and `adom_eval_subset` on a three-way join.
- Selecting on a literal absent from the database leaves an empty active domain.
-/

@[expose] public section

namespace Cslib.Databases.ActiveDomainTests

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

/-- The three-relation database. -/
def db : Fin 3 → Finset (Tuple (Fin 4) ℕ) := ![R, S, T]

theorem db_conforms : Expr.Conforms sch db := by
  intro n
  fin_cases n
  exacts [R_isOver, S_isOver, T_isOver]

/-- The three-way join query type-checks with schema `{A, B, C, E}`, so by `Expr.eval_isOver`
its value on `db` is a relation over that schema. -/
example : IsOver {0, 1, 2, 3}
    ((Expr.join (.join (.rel 0) (.rel 1)) (.rel 2) : Expr (Fin 3) (Fin 4) ℕ).eval db) := by
  exact Expr.eval_isOver db_conforms _ (by decide)

/-- The active domain of `db`, by evaluation. -/
example : adomDB db = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
  decide

/-- `mem_adomDB`, both directions on concrete values. -/
example : (9 : ℕ) ∈ adomDB db ∧ (10 : ℕ) ∉ adomDB db := by
  constructor
  · refine mem_adomDB.mpr
      ⟨1, tup none (some 4) (some 9) none, by decide, 2, by decide⟩
  · intro h
    have hnone : ¬ ∃ n, ∃ t ∈ db n, ∃ a, t a = some (10 : ℕ) := by decide
    exact hnone (mem_adomDB.mp h)

/-- Selecting on a literal absent from the database: the result, and so its active domain, is
empty. The constant `10` does not leak into the output. -/
example : adom ((Expr.select (.eqConst 1 10) (.rel 1) :
    Expr (Fin 3) (Fin 4) ℕ).eval db) = ∅ := by
  decide

/-- `adom_eval_subset` applied to a query (apply the theorem, not `decide`). -/
example : adom ((Expr.project {0, 3} (.join (.rel 0) (.join (.rel 1) (.rel 2))) :
    Expr (Fin 3) (Fin 4) ℕ).eval db) ⊆ adomDB db := by
  exact adom_eval_subset db _

end Cslib.Databases.ActiveDomainTests
