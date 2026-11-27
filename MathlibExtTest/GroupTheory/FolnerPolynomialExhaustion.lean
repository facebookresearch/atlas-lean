/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FolnerPolynomialExhaustion
import Mathlib.Algebra.Group.TypeTags.Basic

open MathlibExt.GroupTheory.FolnerPolynomialSequencePolynomialGrowthKourovka14Problem27Wanted

-- The refutation supplies an actual finitely generated group of non-polynomial growth.
example : ∃ (Γ : Type) (_ : Group Γ) (S : Finset Γ),
    Subgroup.closure (S : Set Γ) = ⊤ ∧ ¬ HasPolynomialGrowth S := by
  by_contra h
  apply polynomialFolnerExhaustionImpliesPolynomialGrowth_refuted
  intro Γ inst S hS F hstrict hexhaust hboundary hsize
  by_contra hg
  exact h ⟨Γ, inst, S, hS, hg⟩

-- For the positive unit step on the integers, the outer boundary of {0} is {-1}.
example : boundary {Multiplicative.ofAdd (1 : ℤ)} {1} =
    ({Multiplicative.ofAdd (-1 : ℤ)} : Set (Multiplicative ℤ)) := by
  ext x
  change (_ ∧ ∃ s ∈ ({Multiplicative.ofAdd (1 : ℤ)} : Finset _), x * s ∈ ({1} : Finset _)) ↔ _
  simp only [Finset.mem_singleton, exists_eq_left, Set.mem_singleton_iff]
  change (x.toAdd ≠ 0 ∧ x.toAdd + 1 = 0) ↔ x.toAdd = -1
  omega

-- At radius zero the empty word gives the identity, for any set of generators.
example {Γ : Type*} [Group Γ] (S : Finset Γ) : wordBall S 0 = {1} := by
  ext g
  constructor
  · rintro ⟨l, hl, _, rfl⟩
    have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    simp [this]
  · rintro (rfl : g = 1)
    exact ⟨[], by simp, by simp, rfl⟩
