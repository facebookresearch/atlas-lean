/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HindmanFiniteSums
import Mathlib.Algebra.Group.Fin.Basic

/-! # Tests for Hindman's finite sums theorem on the natural numbers -/

open MetaMathlibExt

-- Schur's theorem: every finite coloring of `ℕ` has positive `x < y` with `x`, `y` and `x + y` of
-- one color, taken from two members of the infinite set.
example {r : ℕ} (c : ℕ → Fin r) : ∃ x y, 0 < x ∧ x < y ∧ c y = c x ∧ c (x + y) = c x := by
  obtain ⟨A, hA, k, hk⟩ := exists_infinite_finiteSums_monochromatic c
  obtain ⟨x, hx, hx0⟩ := hA.exists_gt 0
  obtain ⟨y, hy, hxy⟩ := hA.exists_gt x
  have h1 := hk {x} (Finset.singleton_nonempty x) (by simpa using hx)
  have h2 := hk {y} (Finset.singleton_nonempty y) (by simpa using hy)
  have h3 := hk {x, y} (Finset.insert_nonempty x {y}) (by simp [Set.insert_subset_iff, hx, hy])
  rw [Finset.sum_singleton] at h1 h2
  rw [Finset.sum_pair hxy.ne] at h3
  exact ⟨x, y, hx0, hxy, h2.trans h1.symm, h3.trans h1.symm⟩

open Fin.NatCast in
-- Colored by residues modulo `m`, the finite sums can only share the residue `0`: two members
-- `x ≠ y` give `k + k = k`. So the infinite set consists of multiples of `m`.
example (m : ℕ) [NeZero m] : ∃ A : Set ℕ, A.Infinite ∧ ∀ a ∈ A, m ∣ a := by
  obtain ⟨A, hA, k, hk⟩ := exists_infinite_finiteSums_monochromatic fun n => (n : Fin m)
  have hk_mem (a : ℕ) (ha : a ∈ A) : (a : Fin m) = k := by
    simpa using hk {a} (Finset.singleton_nonempty a) (by simpa using ha)
  obtain ⟨x, hx, y, hy, hxy⟩ := hA.nontrivial
  have h3 := hk {x, y} (Finset.insert_nonempty x {y}) (by simp [Set.insert_subset_iff, hx, hy])
  rw [Finset.sum_pair hxy, Nat.cast_add, hk_mem x hx, hk_mem y hy] at h3
  have hk0 : k = 0 := add_eq_left.1 h3
  exact ⟨A, hA, fun a ha => Fin.natCast_eq_zero.1 (hk0 ▸ hk_mem a ha)⟩

-- Giving `0` a color of its own does not help: the infinite set has a positive member, so every
-- finite sum gets the color of the positive integers and is positive.
example : ∃ A : Set ℕ, A.Infinite ∧
    ∀ F : Finset ℕ, F.Nonempty → (F : Set ℕ) ⊆ A → 0 < ∑ a ∈ F, a := by
  obtain ⟨A, hA, k, hk⟩ :=
    exists_infinite_finiteSums_monochromatic fun n => if n = 0 then (0 : Fin 2) else 1
  obtain ⟨x, hx, hx0⟩ := hA.exists_gt 0
  have hk1 : k = 1 := by
    simpa [hx0.ne'] using (hk {x} (Finset.singleton_nonempty x) (by simpa using hx)).symm
  refine ⟨A, hA, fun F hF hFA => Nat.pos_of_ne_zero fun h => ?_⟩
  simpa [h, hk1] using hk F hF hFA
