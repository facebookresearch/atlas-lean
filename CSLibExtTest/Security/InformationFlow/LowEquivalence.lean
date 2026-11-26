/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Security.InformationFlow.LowEquivalence
import CSLibExt.Security.Noninterference.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.BooleanAlgebra.Basic

/-!
Tests for low equivalence: the two-point lattice `Bool`, its agreement with the IMP development's
low equivalence, a lattice that is not linear, and the boundary cases of the visibility results.
-/

open Set
open Cslib.Security.InformationFlow

namespace Cslib.Security.InformationFlow.Tests

/-! ### The two-point lattice `L ⊑ H` as `Bool` -/

example : (false : Bool) ≤ true := Bool.false_le _
example : ¬ (true : Bool) ≤ false := by decide
example : (false : Bool) ⊔ true = true := rfl
example : (⊥ : Bool) = false ∧ (⊤ : Bool) = true := ⟨rfl, rfl⟩

/-- Variable `0` is public (`L`) and variable `1` is secret (`H`). -/
def Γ₂ : Fin 2 → Bool := ![false, true]

/-- The observer at `L` sees exactly the public variables. -/
example (σ₁ σ₂ : Fin 2 → ℕ) : LowEquiv Γ₂ false σ₁ σ₂ ↔ σ₁ 0 = σ₂ 0 := by
  simp [lowEquiv_iff, Fin.forall_fin_two, Γ₂]

/-- The observer at `H` sees every variable. -/
example (σ₁ σ₂ : Fin 2 → ℕ) : LowEquiv Γ₂ true σ₁ σ₂ ↔ σ₁ = σ₂ :=
  lowEquiv_top_iff

/-- Stores that differ only in the secret are low equivalent at `L` but not at `H`. -/
example : LowEquiv Γ₂ false ![0, 5] ![(0 : ℕ), 7] ∧ ¬ LowEquiv Γ₂ true ![0, 5] ![(0 : ℕ), 7] := by
  simp [lowEquiv_iff, Fin.forall_fin_two, Γ₂]

/-- Stores that differ in the public variable are not low equivalent at `L`. -/
example : ¬ LowEquiv Γ₂ false ![0, 5] ![(1 : ℕ), 5] := by
  simp [lowEquiv_iff, Fin.forall_fin_two, Γ₂]

/-- At the bottom of any bounded partial order, low equivalence is agreement on the variables of
the least level; for `Bool` this is agreement on the public variables. -/
example (Γ : ℕ → Bool) (σ₁ σ₂ : ℕ → ℕ) :
    LowEquiv Γ false σ₁ σ₂ ↔ ∀ x, Γ x = false → σ₁ x = σ₂ x :=
  lowEquiv_bot_iff

/-- The IMP development's low equivalence is low equivalence at `L` in the two-point lattice. -/
example (Γ : Noninterference.Policy) (s t : Noninterference.Store) :
    Noninterference.LowEquiv Γ s t ↔ LowEquiv Γ false s t :=
  lowEquiv_bot_iff.symm

/-! ### Equivalence and monotonicity -/

example (Γ : ℕ → Bool) (ℓ : Bool) : Equivalence (LowEquiv (α := ℤ) Γ ℓ) :=
  lowEquiv_equivalence Γ ℓ

/-- The definition and the equivalence property need no property of the relation on levels:
here `≤` is the irreflexive relation `≠` on `Bool`. -/
example (Γ : ℕ → Bool) (ℓ : Bool) :
    letI : LE Bool := ⟨fun a b => a ≠ b⟩
    Equivalence (LowEquiv (α := ℕ) Γ ℓ) :=
  letI : LE Bool := ⟨fun a b => a ≠ b⟩
  lowEquiv_equivalence Γ ℓ

/-- What the observer at `H` cannot tell apart, the observer at `L` cannot either. -/
example (σ₁ σ₂ : Fin 2 → ℕ) (h : LowEquiv Γ₂ true σ₁ σ₂) : LowEquiv Γ₂ false σ₁ σ₂ :=
  antitone_lowEquiv Γ₂ (Bool.false_le true) σ₁ σ₂ h

/-- The converse fails. -/
example : ∃ σ₁ σ₂ : Fin 2 → ℕ, LowEquiv Γ₂ false σ₁ σ₂ ∧ ¬ LowEquiv Γ₂ true σ₁ σ₂ :=
  ⟨![0, 5], ![0, 7], by simp [lowEquiv_iff, Fin.forall_fin_two, Γ₂]⟩

/-! ### Permitted flows -/

/-- Copying the public variable into the secret one preserves low equivalence at every level. -/
example : ∀ (ℓ : Bool) (σ₁ σ₂ : Fin 2 → ℕ), LowEquiv Γ₂ ℓ σ₁ σ₂ →
    LowEquiv Γ₂ ℓ (Function.update σ₁ 1 (σ₁ 0)) (Function.update σ₂ 1 (σ₂ 0)) :=
  forall_lowEquiv_update_iff_le.2 (by decide)

/-- Copying the secret into the public variable (an explicit leak) does not. -/
example : ¬ ∀ (ℓ : Bool) (σ₁ σ₂ : Fin 2 → ℕ), LowEquiv Γ₂ ℓ σ₁ σ₂ →
    LowEquiv Γ₂ ℓ (Function.update σ₁ 0 (σ₁ 1)) (Function.update σ₂ 0 (σ₂ 1)) := by
  rw [forall_lowEquiv_update_iff_le]
  decide

/-- The leak, on concrete stores: they agree publicly before the copy and not after it. -/
example : LowEquiv Γ₂ false ![0, 5] ![(0 : ℕ), 7] ∧
    ¬ LowEquiv Γ₂ false (Function.update ![0, 5] 0 5) (Function.update ![(0 : ℕ), 7] 0 7) := by
  simp [lowEquiv_iff, Fin.forall_fin_two, Γ₂]

/-- Copying a variable into itself is always permitted. -/
example (Γ : ℕ → Bool) (x : ℕ) : ∀ (ℓ : Bool) (σ₁ σ₂ : ℕ → ℕ), LowEquiv Γ ℓ σ₁ σ₂ →
    LowEquiv Γ ℓ (Function.update σ₁ x (σ₁ x)) (Function.update σ₂ x (σ₂ x)) :=
  forall_lowEquiv_update_iff_le.2 le_rfl

/-! ### A lattice that is not linear

Levels in `Bool × Bool`, ordered componentwise: variable `0` is at `(true, false)`, variable `1`
at `(false, true)`, and variable `2` at the bottom. -/

/-- A policy into the four-point lattice `Bool × Bool`. -/
def Γ₄ : Fin 3 → Bool × Bool := ![(true, false), (false, true), (false, false)]

/-- Observers at the two incomparable levels see different variables. -/
example : LowEquiv Γ₄ (true, false) ![1, 0, 0] ![(1 : ℕ), 9, 0] ∧
    ¬ LowEquiv Γ₄ (false, true) ![1, 0, 0] ![(1 : ℕ), 9, 0] ∧
    LowEquiv Γ₄ (false, true) ![1, 0, 0] ![(9 : ℕ), 0, 0] ∧
    ¬ LowEquiv Γ₄ (true, false) ![1, 0, 0] ![(9 : ℕ), 0, 0] := by
  simp [lowEquiv_iff, Fin.forall_fin_succ, Γ₄, Prod.le_def]

/-- The information of variables `0` and `1` together is at their join, the top. -/
example : (({0, 1} : Finset (Fin 3)).sup Γ₄) = ⊤ := by decide

/-- So only the observer at the top learns both variables. -/
example (ℓ : Bool × Bool) :
    (∀ σ₁ σ₂ : Fin 3 → ℕ, LowEquiv Γ₄ ℓ σ₁ σ₂ → EqOn σ₁ σ₂ ↑({0, 1} : Finset (Fin 3))) ↔
      ℓ = ⊤ := by
  rw [forall_lowEquiv_eqOn_iff_sup_le, show ({0, 1} : Finset (Fin 3)).sup Γ₄ = ⊤ by decide,
    top_le_iff]

/-- Every observer learns the variable at the bottom. -/
example (ℓ : Bool × Bool) (σ₁ σ₂ : Fin 3 → ℕ) (h : LowEquiv Γ₄ ℓ σ₁ σ₂) : σ₁ 2 = σ₂ 2 :=
  (forall_lowEquiv_eq_iff_le.2 (show Γ₄ 2 ≤ ℓ from bot_le)) σ₁ σ₂ h

/-! ### Boundary cases -/

/-- For two variables, the level of their combined information is the binary join. -/
example {V L : Type*} [DecidableEq V] [SemilatticeSup L] [OrderBot L] (Γ : V → L) (ℓ : L)
    (x y : V) :
    (∀ σ₁ σ₂ : V → ℕ, LowEquiv Γ ℓ σ₁ σ₂ → EqOn σ₁ σ₂ ↑({x, y} : Finset V)) ↔
      Γ x ⊔ Γ y ≤ ℓ := by
  rw [forall_lowEquiv_eqOn_iff_sup_le, Finset.sup_insert, Finset.sup_singleton]

/-- Every observer learns the values of the empty set of variables. -/
example {V L : Type*} [SemilatticeSup L] [OrderBot L] (Γ : V → L) (ℓ : L) :
    ∀ σ₁ σ₂ : V → ℕ, LowEquiv Γ ℓ σ₁ σ₂ → EqOn σ₁ σ₂ ↑(∅ : Finset V) :=
  forall_lowEquiv_eqOn_iff_sup_le.2 (by simp)

/-- With a single value, low equivalence determines every variable, visible or not: the
visibility results need values with at least two elements. -/
example : (∀ σ₁ σ₂ : Fin 2 → Unit, LowEquiv Γ₂ false σ₁ σ₂ → σ₁ 1 = σ₂ 1) ∧ ¬ Γ₂ 1 ≤ false :=
  ⟨fun _ _ _ => rfl, by decide⟩

end Cslib.Security.InformationFlow.Tests
