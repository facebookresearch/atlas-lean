/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebra
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Tests for relational algebra

Attributes are `0, 1, 2 : Fin 3` (think `A`, `B`, `C`) and values are natural numbers.
* `R(A, B)` and `S(B, C)` join on `B` as expected, and the join has schema `{A, B, C}`.
* Selection pushdown, checked by evaluation: `σ_{A = 1}(R ⋈ S) = σ_{A = 1}(R) ⋈ S`; with a
  condition on `C`, which `R` lacks, pushing the selection into `R` changes the result, so the
  side condition of `select_join_left` is needed.
* Projection, renaming, union and difference compute the expected relations.
* Schema inference accepts the join and rejects a union of relations with different schemas;
  query equivalence requires both queries to be well-formed.
-/

@[expose] public section

namespace Cslib.Databases.RelationalAlgebraTests

open Cslib.Databases

/-- The tuple with values `a`, `b`, `c` on the attributes `0`, `1`, `2`. -/
def tup (a b c : Option ℕ) : Tuple (Fin 3) ℕ := ![a, b, c]

/-- `R(A, B)`. -/
def R : Finset (Tuple (Fin 3) ℕ) := {tup (some 1) (some 2) none, tup (some 2) (some 3) none}

/-- `S(B, C)`. -/
def S : Finset (Tuple (Fin 3) ℕ) :=
  {tup none (some 2) (some 5), tup none (some 3) (some 6), tup none (some 4) (some 7)}

theorem R_isOver : IsOver {0, 1} R := by
  unfold IsOver Tuple.IsOver
  decide

theorem S_isOver : IsOver {1, 2} S := by
  unfold IsOver Tuple.IsOver
  decide

example : join R S = {tup (some 1) (some 2) (some 5), tup (some 2) (some 3) (some 6)} := by
  decide

example : IsOver ({0, 1} ∪ {1, 2}) (join R S) := isOver_join R_isOver S_isOver

/-- Selection pushdown on `A = 1`, by evaluation. -/
example : select (.eqConst 0 1) (join R S) = {tup (some 1) (some 2) (some 5)} ∧
    join (select (.eqConst 0 1) R) S = {tup (some 1) (some 2) (some 5)} := by
  decide

/-- ... and by the theorem. -/
example : select (.eqConst 0 1) (join R S) = join (select (.eqConst 0 1) R) S :=
  select_join_left S _ R_isOver (by decide)

/-- Pushing a condition on `C` into `R(A, B)` is wrong: the side condition matters. -/
example : select (.eqConst 2 5) (join R S) ≠ join (select (.eqConst 2 5) R) S := by
  decide

example : project {0} (join R S) = {tup (some 1) none none, tup (some 2) none none} := by
  decide

/-- Renaming `A ↔ C` turns `R(A, B)` into a relation over `{B, C}`. -/
example : rename (Equiv.swap 0 2) R =
    {tup none (some 2) (some 1), tup none (some 3) (some 2)} := by
  decide

example : project {1} R ∪ project {1} S =
    {tup none (some 2) none, tup none (some 3) none, tup none (some 4) none} := by
  decide

example : project {1} S \ project {1} R = {tup none (some 4) none} := by
  decide

/-- On a common schema, the join is the intersection. -/
example : join (project {1} R) (project {1} S) = project {1} R ∩ project {1} S :=
  join_eq_inter (isOver_project R_isOver (by decide)) (isOver_project S_isOver (by decide))

/-- The database schema: relation `0` is `R(A, B)`, relation `1` is `S(B, C)`. -/
def sch : Fin 2 → Finset (Fin 3) := ![{0, 1}, {1, 2}]

/-- The matching database. -/
def db : Fin 2 → Finset (Tuple (Fin 3) ℕ) := ![R, S]

theorem db_conforms : Expr.Conforms sch db := by
  intro n
  fin_cases n
  exacts [R_isOver, S_isOver]

example : (Expr.join (.rel 0) (.rel 1) : Expr (Fin 2) (Fin 3) ℕ).schema sch = some {0, 1, 2} := by
  decide

example : (Expr.union (.rel 0) (.rel 1) : Expr (Fin 2) (Fin 3) ℕ).schema sch = none := by
  decide

example : (Expr.project {0, 2} (.select (.eqAttr 0 0) (.join (.rel 0) (.rel 1))) :
    Expr (Fin 2) (Fin 3) ℕ).eval db =
      {tup (some 1) none (some 5), tup (some 2) none (some 6)} := by
  decide

/-- The pushdown rewrite applies to the query on `R ⋈ S`. -/
example : Expr.Equiv sch (.select (.eqConst 0 1) (.join (.rel 0) (.rel 1)))
    (.join (.select (.eqConst 0 1) (.rel 0)) (.rel 1) : Expr (Fin 2) (Fin 3) ℕ) :=
  Expr.select_join (S := {0, 1}) (S' := {1, 2}) rfl rfl _ (by decide)

/-- Query equivalence requires both sides to be well-formed: `π_{AB}(π_A R)` projects onto an
attribute its operand lacks, so it is not equivalent to anything, although it evaluates to the
same relation as `π_A R`. -/
example : ¬ Expr.Equiv sch (.project {0, 1} (.project {0} (.rel 0)))
    (.project {0} (.rel 0) : Expr (Fin 2) (Fin 3) ℕ) := by
  rintro ⟨S, h, -, -⟩
  have hnone : (Expr.project {0, 1} (.project {0} (.rel 0)) : Expr (Fin 2) (Fin 3) ℕ).schema sch =
      none := by decide
  rw [hnone] at h
  cases h

example : (Expr.project {0, 1} (.project {0} (.rel 0)) : Expr (Fin 2) (Fin 3) ℕ).eval db =
    (Expr.project {0} (.rel 0) : Expr (Fin 2) (Fin 3) ℕ).eval db := by
  decide

end Cslib.Databases.RelationalAlgebraTests
