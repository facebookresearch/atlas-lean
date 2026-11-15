/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Omics.CompositionalCoherence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for subcompositional coherence of CLR.

Every value below is computed by unfolding `clr`, `subcomp`, `closureOp` and `aitchisonDistSq`,
not through the theorems under test, on the composition `x = (1, 2, 4)`, the constant
composition `(1, 1, 1)`, and the subcomposition on `S = {0, 1}`:

* `clr x = (-log 2, 0, log 2)` but `clr (subcomp S x) = (-log 2 / 2, log 2 / 2)`: the CLR of a
  subcomposition is not the restriction of the full CLR, so the re-centring in `clr_subcomp`
  is not vacuous; the re-centred restriction matches the definition;
* the log-ratio `clr i - clr j` is `-log 2` in both;
* the proportion of part `0` is `1 / 7` in the closed full composition and `1 / 3` in the closed
  subcomposition, so proportions are incoherent;
* the squared Aitchison distance to `(1, 1, 1)` drops strictly, from `2 (log 2)²` to
  `(log 2)² / 2`, so dominance is not an equality;
* boundaries: the empty subcomposition (distance `0`), a one-part subcomposition (CLR `0`), and
  `S = univ`. -/

namespace MathlibExtTest.Biology.Omics.CompositionalCoherence

open Finset MathlibExt.Biology.Omics.Normalization MathlibExt.Biology.Omics.CompositionalCoherence

/-- The composition `(1, 2, 4)`. -/
def x124 : PosComposition (Fin 3) := ⟨![1, 2, 4], fun i => by fin_cases i <;> norm_num⟩

/-- The constant composition `(1, 1, 1)`. -/
def x111 : PosComposition (Fin 3) := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The first two parts. -/
def S01 : Finset (Fin 3) := {0, 1}

/-- Part `0` as an element of `S01`. -/
def i0 : S01 := ⟨0, by simp [S01]⟩

/-- Part `1` as an element of `S01`. -/
def i1 : S01 := ⟨1, by simp [S01]⟩

instance : Nonempty S01 := ⟨i0⟩

instance : Nonempty (univ : Finset (Fin 3)) := ⟨⟨0, mem_univ _⟩⟩

theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem sum_S01 (f : Fin 3 → ℝ) : ∑ j : S01, f j = f 0 + f 1 := by
  rw [sum_coe_sort S01 f]
  simp [S01]

theorem card_S01 : Fintype.card S01 = 2 := by
  rw [Fintype.card_coe]
  rfl

/-! ### The full CLR and the subcomposition's CLR, from the definitions -/

theorem clr_x124 : clr x124 = ![-Real.log 2, 0, Real.log 2] := by
  funext i
  fin_cases i <;> simp [clr, x124, Fin.sum_univ_three, log_four] <;> ring

theorem clr_x111 : clr x111 = 0 := by
  funext i
  simp [clr, x111]

theorem clr_subcomp_x124_i0 : clr (subcomp S01 x124) i0 = -(Real.log 2 / 2) := by
  simp only [clr, subcomp, card_S01]
  rw [sum_S01 (fun k => Real.log (x124.1 k))]
  simp [x124, i0]

theorem clr_subcomp_x124_i1 : clr (subcomp S01 x124) i1 = Real.log 2 / 2 := by
  simp only [clr, subcomp, card_S01]
  rw [sum_S01 (fun k => Real.log (x124.1 k))]
  simp [x124, i1]
  ring

theorem clr_subcomp_x111 (i : S01) : clr (subcomp S01 x111) i = 0 := by
  simp only [clr, subcomp, card_S01]
  rw [sum_S01 (fun k => Real.log (x111.1 k))]
  simp [x111]

/-- Non-vacuity of the re-centring: the subcomposition's CLR is not the restricted full CLR. -/
example : clr (subcomp S01 x124) i0 ≠ clr x124 0 := by
  rw [clr_subcomp_x124_i0, clr_x124]
  simp only [Matrix.cons_val_zero]
  linarith [log_two_pos]

/-- The re-centred restriction of the full CLR, computed directly, is the subcomposition's CLR. -/
example : clr x124 0 - (∑ j ∈ S01, clr x124 j) / #S01 = clr (subcomp S01 x124) i0 := by
  rw [clr_subcomp_x124_i0, clr_x124]
  simp [S01]
  ring

example : clr (subcomp S01 x124) i0 = clr x124 0 - (∑ j ∈ S01, clr x124 j) / #S01 :=
  clr_subcomp S01 x124 i0

/-! ### Log-ratio coherence -/

/-- Both differences are `-log 2`, computed separately. -/
example : clr (subcomp S01 x124) i0 - clr (subcomp S01 x124) i1 = clr x124 0 - clr x124 1 := by
  rw [clr_subcomp_x124_i0, clr_subcomp_x124_i1, clr_x124]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

example : clr (subcomp S01 x124) i0 - clr (subcomp S01 x124) i1 = Real.log (1 / 2) := by
  rw [clr_subcomp_x124_i0, clr_subcomp_x124_i1, one_div, Real.log_inv]
  ring

example : clr (subcomp S01 x124) i0 - clr (subcomp S01 x124) i1 = clr x124 0 - clr x124 1 :=
  clr_subcomp_sub_clr_subcomp S01 x124 i0 i1

/-! ### Proportions are incoherent -/

theorem closureOp_x124_zero : (closureOp x124).1 0 = 1 / 7 := by
  norm_num [closureOp, x124, Fin.sum_univ_three]

theorem closureOp_subcomp_x124_i0 : (closureOp (subcomp S01 x124)).1 i0 = 1 / 3 := by
  simp only [closureOp, subcomp]
  rw [sum_S01 (fun k => x124.1 k)]
  norm_num [x124, i0]

example : (closureOp (subcomp S01 x124)).1 i0 ≠ (closureOp x124).1 0 := by
  rw [closureOp_subcomp_x124_i0, closureOp_x124_zero]
  norm_num

/-- The contrast theorem agrees: `S01` misses part `2`. -/
example : (closureOp (subcomp S01 x124)).1 i0 ≠ (closureOp x124).1 i0 := by
  rw [Ne, closureOp_subcomp_apply_eq_iff]
  intro h
  have : (2 : Fin 3) ∈ S01 := h ▸ mem_univ _
  simp [S01] at this

/-! ### Subcompositional dominance, strictly -/

theorem aitchisonDistSq_x124_x111 : aitchisonDistSq x124 x111 = 2 * Real.log 2 ^ 2 := by
  simp [aitchisonDistSq, clr_x124, clr_x111, Fin.sum_univ_three]
  ring

theorem aitchisonDistSq_subcomp_x124_x111 :
    aitchisonDistSq (subcomp S01 x124) (subcomp S01 x111) = Real.log 2 ^ 2 / 2 := by
  have h : ∀ i : S01, (clr (subcomp S01 x124) i - clr (subcomp S01 x111) i) ^ 2 =
      (Real.log 2 / 2) ^ 2 := by
    rintro ⟨k, hk⟩
    rw [clr_subcomp_x111]
    simp only [S01, mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · rw [show (⟨0, _⟩ : S01) = i0 from rfl, clr_subcomp_x124_i0]; ring
    · rw [show (⟨1, _⟩ : S01) = i1 from rfl, clr_subcomp_x124_i1]; ring
  unfold aitchisonDistSq
  simp_rw [h]
  rw [sum_const, card_univ, card_S01]
  simp
  ring

example : aitchisonDistSq (subcomp S01 x124) (subcomp S01 x111) < aitchisonDistSq x124 x111 := by
  rw [aitchisonDistSq_subcomp_x124_x111, aitchisonDistSq_x124_x111]
  have := log_two_pos
  nlinarith

example : aitchisonDistSq (subcomp S01 x124) (subcomp S01 x111) ≤ aitchisonDistSq x124 x111 :=
  aitchisonDistSq_subcomp_le S01 x124 x111

/-! ### Boundaries -/

/-- The empty subcomposition: distance `0`, from the definition. -/
example (x y : PosComposition (Fin 3)) :
    aitchisonDistSq (subcomp (∅ : Finset (Fin 3)) x) (subcomp ∅ y) = 0 := by
  simp [aitchisonDistSq]

/-- A one-part subcomposition has CLR `0`, from the definition. -/
example (x : PosComposition (Fin 3)) (i : ({2} : Finset (Fin 3))) :
    clr (subcomp {2} x) i = 0 := by
  obtain ⟨k, hk⟩ := i
  rw [mem_singleton] at hk
  subst hk
  simp [clr, subcomp]

/-- `S = univ`: the full CLR and the full proportions. -/
example (x : PosComposition (Fin 3)) (i : (univ : Finset (Fin 3))) :
    clr (subcomp univ x) i = clr x i :=
  clr_subcomp_univ x i

example (x : PosComposition (Fin 3)) (i : (univ : Finset (Fin 3))) :
    (closureOp (subcomp univ x)).1 i = (closureOp x).1 i :=
  (closureOp_subcomp_apply_eq_iff univ x i).2 rfl

/-- Closure: total `1` and the same CLR, on `(1, 2, 4)`. -/
example : ∑ i, (closureOp x124).1 i = 1 := sum_closureOp x124

example : clr (subcomp S01 (closureOp x124)) = clr (subcomp S01 x124) :=
  clr_subcomp_closureOp S01 x124

example : clr (subcomp S01 (x124.smul 3 (by norm_num))) = clr (subcomp S01 x124) :=
  clr_subcomp_smul S01 3 (by norm_num) x124

end MathlibExtTest.Biology.Omics.CompositionalCoherence
