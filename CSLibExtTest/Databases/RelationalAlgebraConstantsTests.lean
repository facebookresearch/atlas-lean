/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.RelationalAlgebraConstants
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Tests for relational algebra with constants

Attributes are `0, 1 : Fin 2` (think `A`, `B`); values are natural numbers.
- The one-relation database `db` over `R(A)`, and the proof that it conforms to its schema.
- The constant queries `q₁` (a cross product with `{⟨B : 5⟩}`) and `q₂` (`R` extended by
  `{⟨A : 7⟩}`): schemas, values and constants, all by evaluation.
- The active-domain bound on `q₂`, and strictness of the extension: no constant-free query
  computes `q₂` on this database.
- A lifted rewrite on a query with a constant, selection pushdown into a constant operand,
  and conservativity on a constant-free query.
-/

@[expose] public section

namespace Cslib.Databases.RelationalAlgebraConstantsTests

open Cslib.Databases ConstExpr

/-- The tuple with values `a`, `b` on the attributes `0`, `1` (think `A`, `B`). -/
def tup (a b : Option ℕ) : Tuple (Fin 2) ℕ := ![a, b]

/-- One base relation `R(A)`. -/
def sch : Fin 1 → Finset (Fin 2) := fun _ => {0}

/-- `R = {⟨A : 1⟩, ⟨A : 2⟩}`. -/
def db : Fin 1 → Finset (Tuple (Fin 2) ℕ) := fun _ => {tup (some 1) none, tup (some 2) none}

/-- The one-relation database `db` conforms to its schema `sch`. -/
theorem db_conforms : Expr.Conforms sch db := by
  intro n
  fin_cases n
  unfold IsOver Tuple.IsOver
  decide

/-- `R ⋈ {⟨B : 5⟩}`, a cross product with a constant. -/
def q₁ : ConstExpr (Fin 1) (Fin 2) ℕ := .join (.rel (.inl 0)) (const 1 5)

/-- `R ∪ {⟨A : 7⟩}`. -/
def q₂ : ConstExpr (Fin 1) (Fin 2) ℕ := .union (.rel (.inl 0)) (const 0 7)

/-- `q₁` has schema `{0, 1}`, by evaluation. -/
theorem schema_q₁ : q₁.schema sch = some {0, 1} := by
  decide

/-- `q₁` evaluates to the two expected tuples, by evaluation. -/
theorem eval_q₁ : q₁.eval db = {tup (some 1) (some 5), tup (some 2) (some 5)} := by
  decide

/-- `q₂` has schema `{0}`, by evaluation. -/
theorem schema_q₂ : q₂.schema sch = some {0} := by
  decide

/-- `q₂` evaluates to `R` extended by `⟨A : 7⟩`, by evaluation. -/
theorem eval_q₂ : q₂.eval db = {tup (some 1) none, tup (some 2) none, tup (some 7) none} := by
  decide

/-- The only constant value of `q₂` is `7`, by evaluation. -/
theorem consts_q₂ : q₂.consts = {7} := by
  decide

/-- `7` occurs nowhere in `db`, by evaluation. -/
theorem seven_not_mem_adom : 7 ∉ adomDB db := by
  decide

/-- `7` occurs in the value of `q₂`, by evaluation. -/
theorem seven_mem_adom_eval : 7 ∈ adom (q₂.eval db) := by
  decide

/-- `ConstExpr.adom_eval_subset` instantiated: the only new value of `q₂` is its constant `7`. -/
theorem adom_eval_q₂ : adom (q₂.eval db) ⊆ adomDB db ∪ {7} := by
  have h := ConstExpr.adom_eval_subset db q₂
  rw [consts_q₂] at h
  exact h

/-- The extension is strict: no constant-free query computes `q₂` on `db`. -/
theorem not_exists_expr_eval_eq : ¬ ∃ e : Expr (Fin 1) (Fin 2) ℕ, e.eval db = q₂.eval db := by
  rintro ⟨e, he⟩
  have hsub := Cslib.Databases.adom_eval_subset db e
  rw [he] at hsub
  exact seven_not_mem_adom (hsub seven_mem_adom_eval)

/-- A landed law, lifted, on a query with a constant. -/
theorem join_comm_q₁ :
    Equiv sch (.join (.rel (.inl 0)) (const 1 5)) (.join (const 1 5) (.rel (.inl 0))) := by
  exact ConstExpr.join_comm (S := {0}) (S' := {1}) (by decide) (by decide)

/-- Selection pushdown into a constant operand. -/
theorem select_join_right_q₁ :
    Equiv sch (.select (.eqConst 1 5) q₁)
      (.join (.rel (.inl 0)) (.select (.eqConst 1 5) (const 1 5))) := by
  exact ConstExpr.select_join_right (S := {0}) (S' := {1}) (by decide) (by decide) _ (by decide)

/-- Conservativity on a constant-free query. -/
theorem eval_ofExpr_rel :
    (ofExpr (.rel 0) : ConstExpr (Fin 1) (Fin 2) ℕ).eval db = db 0 := by
  exact eval_ofExpr db (.rel 0)

end Cslib.Databases.RelationalAlgebraConstantsTests
