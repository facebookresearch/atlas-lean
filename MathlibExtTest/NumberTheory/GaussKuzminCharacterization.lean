/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminCharacterization

/-! # Tests for the characterization of the Gauss–Kuzmin density by reversal symmetry -/

open MetaMathlibExt MeasureTheory Real

-- Symmetry for strings of every length pins down the density at the right endpoint.
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    f 1 = 1 / (2 * log 2) := by
  rw [density_eq_gaussKuzmin_of_reverse_symmetric f hf hf0 hf1 Set.univ Set.infinite_univ
    (fun a ha _ => hsym a ha) 1 ⟨zero_le_one, le_rfl⟩]
  ring

-- Symmetry for strings of even length only is enough: the value at `1/2` is `2 / (3 log 2)`.
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → Even a.length →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    f (1 / 2) = 2 / (3 * log 2) := by
  have hS : {n : ℕ | Even n}.Infinite :=
    Set.infinite_of_forall_exists_gt fun n => ⟨2 * n + 2, ⟨n + 1, by ring⟩, by omega⟩
  rw [density_eq_gaussKuzmin_of_reverse_symmetric f hf hf0 hf1 {n | Even n} hS hsym (1 / 2)
    ⟨by norm_num, by norm_num⟩]
  field_simp
  ring

-- Symmetry for long strings only (length at least `5`) already fixes `f 0 = 1 / log 2`.
example (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) (hf1 : ∫ x in (0 : ℝ)..1, f x = 1)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → 5 ≤ a.length →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    f 0 = 1 / log 2 := by
  rw [density_eq_gaussKuzmin_of_reverse_symmetric f hf hf0 hf1 (Set.Ici 5) (Set.Ici_infinite 5)
    hsym 0 ⟨le_rfl, zero_le_one⟩]
  simp

-- The uniform density is not reversal symmetric along any infinite set of lengths, since
-- `log 2 ≠ 1`.
example (S : Set ℕ) (hS : S.Infinite) :
    ¬ ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ∈ S →
      ∫ _ in cfCylinder a, (1 : ℝ) = ∫ _ in cfCylinder a.reverse, (1 : ℝ) := by
  intro hsym
  have h := density_eq_gaussKuzmin_of_reverse_symmetric (fun _ => 1) continuousOn_const
    (fun _ _ => zero_le_one) (by simp) S hS hsym 0 ⟨le_rfl, zero_le_one⟩
  have hlog : log 2 < 2 - 1 := log_lt_sub_one_of_pos two_pos (by norm_num)
  norm_num at h
  linarith
