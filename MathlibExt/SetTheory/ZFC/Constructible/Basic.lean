/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import Mathlib.Data.Fin.Basic
@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 328
-- Proposed path (advisory metadata only, not a review instruction).

-- Logic 328: Formulas in the language of set theory
inductive SetFormula : ℕ → Type
  | mem {n} : Fin n → Fin n → SetFormula n
  | eq {n} : Fin n → Fin n → SetFormula n
  | neg {n} : SetFormula n → SetFormula n
  | or {n} : SetFormula n → SetFormula n → SetFormula n
  | ex {n} : SetFormula (n + 1) → SetFormula n


theorem sentence_not_atomic (φ : SetFormula 0) :
    (∃ ψ, φ = .neg ψ) ∨ (∃ ψ χ, φ = .or ψ χ) ∨ (∃ ψ, φ = .ex ψ) := by
  cases φ with
  | mem i j => exact i.elim0
  | eq i j => exact i.elim0
  | neg ψ => exact Or.inl ⟨ψ, rfl⟩
  | or ψ χ => exact Or.inr (Or.inl ⟨ψ, χ, rfl⟩)
  | ex ψ => exact Or.inr (Or.inr ⟨ψ, rfl⟩)

end
