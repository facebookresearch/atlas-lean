/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Chain
import Mathlib.Data.Matrix.Basis
import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitz
import MathlibExt.KTheory.Ring.K2.StableSteinbergUpperUnipotentCollection

/-! # Concrete clients of Steinberg collection and finite Hurwitz shortening -/

open AlgebraicKTheory AlgebraicKTheory.StableSteinberg
open scoped commutatorElement

namespace MathlibExtTest.SteinbergCollectionClients

private abbrev R := Matrix (Fin 2) (Fin 2) ℤ

private def u : R := Matrix.single 0 1 1
private def v : R := Matrix.single 1 0 1
private def e₀₀ : R := Matrix.single 0 0 1
private def e₁₁ : R := Matrix.single 1 1 1

private theorem uv : u * v = e₀₀ := by simp [u, v, e₀₀]
private theorem vu : v * u = e₁₁ := by simp [u, v, e₁₁]

/-- Reversing the order of coefficient multiplication changes the matrix. -/
example : u * v ≠ v * u := by
  rw [uv, vu]
  intro h
  have hEntry := congrArg (fun A : R => A 0 0) h
  simp [e₀₀, e₁₁] at hEntry

/-- The actual quotient generators use the upper-left matrix unit, not the lower-right one. -/
example : ⁅x 0 1 (by decide) u, x 1 2 (by decide) v⁆ = x 0 2 (by decide) e₀₀ := by
  rw [← uv]
  exact x_chev 0 1 2 (by decide) (by decide) (by decide) u v

/-- The mixed swap uses the negative correction on the left in head-left order. -/
example : x 1 2 (by decide) v * x 0 1 (by decide) u =
    x 0 2 (by decide) (-e₀₀) * (x 0 1 (by decide) u * x 1 2 (by decide) v) := by
  rw [← uv]
  exact upperUnipotent_mixedSwap_chev (a := 0) (b := 1) (n := 2) (by decide) (by decide) u v

/-- The reversed pair is in rank three and has a representation supported on positive roots. -/
example : ∃ c : ℕ × ℕ → R,
    x 1 2 (by decide) v * x 0 1 (by decide) u = upperUnipotentProd 3 c ∧
    ∀ p ∉ orderedPositiveRoots 3, c p = 0 := by
  apply upperUnipotentSubgroup_exists_prod_repr
  exact (upperUnipotentSubgroup (R := R) 3).mul_mem
    (x_mem_upperUnipotentSubgroup (by decide) (by decide) (by decide) (by decide) v)
    (x_mem_upperUnipotentSubgroup (by decide) (by decide) (by decide) (by decide) u)

example : finiteStage (R := R) 0 = ⊥ ∧ upperUnipotentProd 0 (fun _ => u) = 1 :=
  ⟨finiteStage_zero_eq_bot, upperUnipotentProd_zero _⟩

example : finiteStage (R := R) 1 = ⊥ ∧ upperUnipotentProd 1 (fun _ => v) = 1 :=
  ⟨finiteStage_one_eq_bot, upperUnipotentProd_one _⟩

private def swap₀₁ : SwapLabel 3 := ⟨(0, 1), by decide⟩
private def swap₁₂ : SwapLabel 3 := ⟨(1, 2), by decide⟩
private def swap₀₂ : SwapLabel 3 := ⟨(0, 2), by decide⟩

private def word : List (SwapLabel 3) := [swap₀₁, swap₁₂, swap₀₁, swap₀₂]

private theorem word_prod_one : wordProd word = 1 := by
  ext i
  fin_cases i <;> decide

private theorem swap₀₁_ne_swap₁₂ : swapDenote swap₀₁ ≠ swapDenote swap₁₂ := by
  intro h
  have hPoint := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) h
  exact (by decide : (1 : Fin 3) ≠ 0) hPoint

private theorem swap₀₁_ne_swap₀₂ : swapDenote swap₀₁ ≠ swapDenote swap₀₂ := by
  intro h
  have hPoint := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 1) h
  exact (by decide : (0 : Fin 3) ≠ 1) hPoint

/-- A nonempty product-one word must move before it can delete an equal-denotation pair. -/
example : word.IsChain (fun a b => swapDenote a ≠ swapDenote b) ∧
    ∃ pre a b suf, HurwitzReach word (pre ++ [a, b] ++ suf) ∧
      swapDenote a = swapDenote b ∧ wordProd (pre ++ suf) = 1 ∧
      (pre ++ suf).length = 2 := by
  refine ⟨?_, ?_⟩
  · simp only [word, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨swap₀₁_ne_swap₁₂, Ne.symm swap₀₁_ne_swap₁₂, swap₀₁_ne_swap₀₂⟩
  · obtain ⟨pre, a, b, suf, hReach, hEqual, hProd, hLen⟩ :=
      exists_hurwitz_adjacent_equal word (by decide) word_prod_one
    have hFour : word.length = 4 := rfl
    exact ⟨pre, a, b, suf, hReach, hEqual, hProd, by omega⟩

end MathlibExtTest.SteinbergCollectionClients
