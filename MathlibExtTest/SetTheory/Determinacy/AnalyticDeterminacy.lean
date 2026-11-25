/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.AnalyticDeterminacy

@[expose] public section

open Set MeasureTheory MathlibExt.SetTheory.Determinacy
open MathlibExt.SetTheory.DeterminacyWanted

namespace MathlibExtTest.SetTheory.Determinacy.AnalyticDeterminacy

universe u

variable {κ : Cardinal.{u}}

/-- The range of any continuous map of Baire space is determined, given a measurable cardinal. -/
example (hκ : MetaMathlibExt.IsMeasurable κ) {f : (ℕ → ℕ) → ℕ → ℕ} (hf : Continuous f) :
    Determined (range f) :=
  determined_of_analyticSet_of_isMeasurable hκ (analyticSet_range_of_polishSpace hf)

/-- The projection of a closed subset of `ℕ^ℕ × ℕ^ℕ`, the typical analytic set, is determined. -/
example (hκ : MetaMathlibExt.IsMeasurable κ) {C : Set ((ℕ → ℕ) × (ℕ → ℕ))} (hC : IsClosed C) :
    Determined {x : ℕ → ℕ | ∃ y, (x, y) ∈ C} := by
  have : {x : ℕ → ℕ | ∃ y, (x, y) ∈ C} = Prod.fst '' C := by
    ext x
    simp
  rw [this]
  exact determined_of_analyticSet_of_isMeasurable hκ
    (hC.analyticSet.image_of_continuous continuous_fst)

/-- A countable union of continuous images of Baire space is analytic, hence determined. -/
example (hκ : MetaMathlibExt.IsMeasurable κ) {f : ℕ → (ℕ → ℕ) → ℕ → ℕ}
    (hf : ∀ n, Continuous (f n)) : Determined (⋃ n, range (f n)) :=
  determined_of_analyticSet_of_isMeasurable hκ
    (AnalyticSet.iUnion fun n => analyticSet_range_of_polishSpace (hf n))

/-- Closed sets are analytic, so the theorem also covers the closed case of the Gale–Stewart
theorem; the measurable cardinal may live in a higher universe than the moves. -/
example {κ : Cardinal.{2}} (hκ : MetaMathlibExt.IsMeasurable κ) :
    Determined {x : ℕ → ℕ | ∀ n, x (2 * n) = 0} := by
  have hS : IsClosed {x : ℕ → ℕ | ∀ n, x (2 * n) = 0} := by
    have : {x : ℕ → ℕ | ∀ n, x (2 * n) = 0} = ⋂ n, (fun x : ℕ → ℕ => x (2 * n)) ⁻¹' {0} := by
      ext x
      simp
    rw [this]
    exact isClosed_iInter fun n => (isClosed_discrete _).preimage (continuous_apply _)
  exact determined_of_analyticSet_of_isMeasurable hκ hS.analyticSet

/-- The empty set is analytic and determined (player II wins it). -/
example (hκ : MetaMathlibExt.IsMeasurable κ) : Determined (∅ : Set (ℕ → ℕ)) :=
  determined_of_analyticSet_of_isMeasurable hκ analyticSet_empty

/-- With a measurable cardinal, exactly one player wins each analytic game. -/
example (hκ : MetaMathlibExt.IsMeasurable κ) {S : Set (ℕ → ℕ)} (hS : AnalyticSet S) :
    (IWins S ∧ ¬ IIWins S) ∨ (IIWins S ∧ ¬ IWins S) := by
  rcases determined_of_analyticSet_of_isMeasurable hκ hS with h | h
  · exact Or.inl ⟨h, fun h' => not_iWins_and_iiWins S ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => not_iWins_and_iiWins S ⟨h', h⟩⟩

end MathlibExtTest.SetTheory.Determinacy.AnalyticDeterminacy
