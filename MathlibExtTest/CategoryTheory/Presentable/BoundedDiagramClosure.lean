/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Presentable.BoundedDiagramClosure
import Mathlib.Data.Finset.Image

/-!
A fixed regular cardinal bounds action-compatible filtered families of
finite subsets of an arbitrary carrier. No cardinal bound on the carrier
is an assumption. The original action function is used on every subset.
-/

set_option autoImplicit false
noncomputable section

universe w

open CategoryTheory Limits CategoryTheory.Presentable.BoundedDiagramClosure

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {Γ : Type w} [DecidableEq Γ]

/-- Apply the original action to the finite union of the supplied indices. -/
def actionConstraint (a : Γ → Γ) (_ : PUnit.{1}) (xs : List (Finset Γ)) : Finset Γ :=
  (xs.foldr (fun s t : Finset Γ => s ∪ t) ∅).image a

/-- The entire carrier can be large; only the produced compatible index family is bounded. -/
example (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : Cardinal.aleph0.{w}.SharplyLT κ) (a : Γ → Γ) (seed : Finset Γ) :
    ∃ (B : Set (Finset Γ)), seed ∈ B ∧ IsCardinalFiltered B Cardinal.aleph0.{w} ∧
      HasCardinalLT B κ ∧ ∀ (s : Finset Γ), s ∈ B → s.image a ∈ B := by
  have : IsFiltered (Finset Γ) := inferInstance
  have : IsCardinalFiltered (Finset Γ) Cardinal.aleph0.{w} :=
    (isCardinalFiltered_aleph0_iff _).mpr inferInstance
  have hκ : Cardinal.aleph0.{w} ≤ κ := h.le
  obtain ⟨B, hSeed, hFiltered, hSmall, hAction⟩ :=
    exists_closed_bounded_filtered_set h (actionConstraint a)
      (hasCardinalLT_of_finite PUnit.{1} κ hκ) ({seed} : Set (Finset Γ))
      (hasCardinalLT_of_finite _ κ hκ)
  refine ⟨B, hSeed (by simp), hFiltered, hSmall, ?_⟩
  intro s hs
  simpa [actionConstraint] using hAction PUnit.unit [⟨s, hs⟩]
