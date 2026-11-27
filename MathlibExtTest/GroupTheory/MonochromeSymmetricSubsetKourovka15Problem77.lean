/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.ZMod.Basic

/-! # Tests for monochromatic symmetric subsets of abelian groups -/

open MathlibExt.GroupTheory.MonochromeSymmetricSubsetKourovka15Problem77Wanted
open Cardinal Set

-- An odd finite size in a torsion-free group, with symmetry stated as equality of sets.
example (χ : ℤ → Fin 4) : ∃ (A : Set ℤ) (c : Fin 4) (g : ℤ),
    #A = 3 ∧ (∀ a ∈ A, χ a = c) ∧ (fun a ↦ g + g - a) '' A = A := by
  obtain ⟨A, hA, ⟨c, hc⟩, g, hg⟩ := monochromeSymmetricSubsetExists_holds ℤ inferInstance 3
    (by simp) 4 χ
  refine ⟨A, c, g, hA, hc, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hg a ha
  · intro a ha
    exact ⟨_, hg a ha, sub_sub_cancel _ _⟩

-- A countably infinite monochromatic symmetric subset of the additive reals.
example {n : ℕ} (χ : ℝ → Fin n) : ∃ (A : Set ℝ) (c : Fin n) (g : ℝ),
    A.Countable ∧ A.Infinite ∧ (∀ a ∈ A, χ a = c) ∧ ∀ a ∈ A, g + g - a ∈ A := by
  obtain ⟨A, hA, ⟨c, hc⟩, g, hg⟩ := monochromeSymmetricSubsetExists_holds ℝ inferInstance ℵ₀
    (by rw [mk_real]; exact aleph0_lt_continuum) n χ
  exact ⟨A, c, g, le_aleph0_iff_set_countable.mp hA.le, aleph0_le_mk_set.mp hA.ge, hc, hg⟩

-- In a Boolean group the theorem also applies when doubling has singleton range.
example (χ : (ℕ → ZMod 2) → Fin 2) : ∃ (A : Set (ℕ → ZMod 2)) (c : Fin 2),
    #A = ℵ₀ ∧ ∀ a ∈ A, χ a = c := by
  have h : ℵ₀ < #(ℕ → ZMod 2) := by
    simpa [mk_arrow, mk_fintype, ZMod.card] using cantor ℵ₀
  obtain ⟨A, hA, ⟨c, hc⟩, _⟩ :=
    monochromeSymmetricSubsetExists_holds (ℕ → ZMod 2) inferInstance ℵ₀ h 2 χ
  exact ⟨A, c, hA, hc⟩
