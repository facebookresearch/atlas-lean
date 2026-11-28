/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FiniteMultipleZetaLevelColoredFiniteMZVOneEqPowMulSumProd
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases

/-! # Tests for raising the level of finite multiple zeta values -/

open Filter MetaMathlibExt

private def oddColor (a : ZMod 2) : Option (Fin 1 → ZMod 2) :=
  if a = 1 then some (fun _ => 1) else none

private def oddLift (b : Fin 4) (a : ZMod 4) : Option (Fin 1 → ZMod 4) :=
  if (a = 1 ∨ a = 3) ∧ (b = 1 ∨ b = 3) then some (fun _ => (b.val : ZMod 4)) else none

-- At `p = 5`, the low color selects `1, 3`, whose inverses are `1, 2`.
example : finiteMZVColored 5 2 (fun _ : Fin 1 => 1) oddColor = 3 := by
  rw [finiteMZVColored_eq_sum_ite]
  decide +kernel

-- The two odd colors contribute separately; the even colors are disabled.
example (b : Fin 4) :
    finiteMZVColored 5 4 (fun _ : Fin 1 => 1) (oddLift b) = ![0, 1, 0, 2] b := by
  fin_cases b <;> rw [finiteMZVColored_eq_sum_ite] <;> decide +kernel

-- Use explicit unit coefficients and lift every index unchanged at depth one.
example : (∀ (_ : Fin 4) (j : Fin 1), 0 < (fun _ : Fin 1 => 1) j) ∧
    (∀ _ : Fin 4, (∑ _ : Fin 1, (1 : ℕ)) = 1) ∧
    finiteMZVColored 5 2 (fun _ : Fin 1 => 1) oddColor =
      ∑ b : Fin 4, finiteMZVColored 5 4 (fun _ : Fin 1 => 1) (oddLift b) := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [finiteMZVColored_eq_sum_ite]
  decide +kernel

-- With weights `1, 2`, only the ordered pair `(1, 3)` contributes at depth two.
example : finiteMZVColored 5 2 ![1, 2] (fun _ => some ![1, 1]) = 4 ∧
    finiteMZVColored 5 4 ![1, 2] (fun _ => some ![1, 3]) = 4 ∧
    finiteMZVColored 5 4 ![1, 2] (fun _ => some ![3, 1]) = 0 := by
  simp only [finiteMZVColored_eq_sum_ite]
  decide +kernel

-- At weight zero, the selected empty tuple contributes `1`; `none` contributes `0`.
example : (∑ _ : Fin 0, (0 : ℕ)) = 0 ∧
    finiteMZVColored 5 2 (fun _ : Fin 0 => 0) (fun _ => some (fun _ => 0)) = 1 ∧
    finiteMZVColored 5 4 (fun _ : Fin 0 => 0) (fun _ => some (fun _ => 0)) = 1 ∧
    finiteMZVColored 5 2 (fun _ : Fin 0 => 0) (fun _ => none) = 0 ∧
    finiteMZVColored 5 4 (fun _ : Fin 0 => 0) (fun _ => none) = 0 := by
  simp only [finiteMZVColored_eq_sum_ite]
  decide +kernel

-- At the prime `2`, which divides both levels, the low and lifted maps select no color.
example : finiteMZVColored 2 2 (fun _ : Fin 1 => 1) oddColor = 0 ∧
    ∀ b : Fin 4, finiteMZVColored 2 4 (fun _ : Fin 1 => 1) (oddLift b) = 0 := by
  simp only [finiteMZVColored_eq_sum_ite]
  decide +kernel

-- Client of the eventual theorem at the same two levels.
example : ∃ (n : ℕ) (q : Fin n → ℚ) (s : Fin n → ℕ) (k' : (i : Fin n) → Fin (s i) → ℕ)
    (c' : (i : Fin n) → ZMod 4 → Option (Fin (s i) → ZMod 4)),
    (∀ i j, 0 < k' i j) ∧ (∀ i, ∑ j, k' i j = 1) ∧
      ∀ᶠ p in atTop, p.Prime →
        finiteMZVColored p 2 (fun _ : Fin 1 => 1) oddColor =
          ∑ i, ((q i).num : ZMod p) * ((q i).den : ZMod p)⁻¹ * finiteMZVColored p 4 (k' i) (c' i) := by
  simpa using exists_finiteMZVColored_eq_sum_of_dvd (N := 2) (M := 4) (by decide) (by decide)
    (by decide) (fun _ : Fin 1 => 1) (fun _ => by decide) oddColor
