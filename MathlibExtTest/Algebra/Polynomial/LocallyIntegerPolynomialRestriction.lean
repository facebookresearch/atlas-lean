/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Order.Interval.Set.Infinite
import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomialRestriction

/-! # Tests for restriction of locally integer polynomial functions -/

open MetaMathlibExt

-- Agreement on the nonnegative integers determines the values even at negative integers.
example {f g : ↥(Set.univ : Set ℤ) → ℤ} (hf : f ∈ lipSubring Set.univ)
    (hg : g ∈ lipSubring Set.univ)
    (h : ∀ x : Set.Ici (0 : ℤ), f ⟨x, Set.mem_univ _⟩ = g ⟨x, Set.mem_univ _⟩) : f = g :=
  lip_restrict_injective (Set.Ici_infinite 0) (Set.subset_univ _) hf hg (funext h)

-- A singleton does not suffice: the identity and zero agree at 0 but differ at 1.
example : ∃ f g : ↥(Set.univ : Set ℤ) → ℤ, f ∈ lipSubring Set.univ ∧ g ∈ lipSubring Set.univ ∧
    f ⟨0, Set.mem_univ _⟩ = g ⟨0, Set.mem_univ _⟩ ∧ f ≠ g := by
  refine ⟨Subtype.val, 0, ?_, (lipSubring Set.univ).zero_mem, rfl, ?_⟩
  · exact mem_lipSubring_iff.mpr fun _ => ⟨Polynomial.X, fun _ _ => Polynomial.eval_X⟩
  · intro h
    exact one_ne_zero (congrFun h ⟨1, Set.mem_univ _⟩ : (1 : ℤ) = 0)
