/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Admixture.FourPoint
import MathlibExt.Biology.PopulationGenetics.Admixture.ConditionalNegDef

/-! Tests for the quartet f4 trichotomy: generic restatements and concrete
realized models (quartet split, zero internal branch, and the square, whose
binary loadings do not give the split conclusion). -/

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.Phylogenetics.Buneman
open scoped symmDiff

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.FourPoint

example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}
    (hp : ∀ X, MemLp (p X) 2 μ) (A B C D : P) :
    f4 μ p A B C D = (f2 μ p A D + f2 μ p B C - f2 μ p A C - f2 μ p B D) / 2 :=
  f4_eq_f2 hp A B C D

example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}
    (hp : ∀ X, MemLp (p X) 2 μ) (h : FourPointCondition (f2 μ p)) (A B C D : P) :
    f4 μ p A B C D = 0 ∨ f4 μ p A C B D = 0 ∨ f4 μ p A D B C = 0 :=
  f4_eq_zero_or_of_fourPointCondition hp h A B C D

open MathlibExt.Biology.PopulationGenetics.FStatistics
open MathlibExt.Biology.PopulationGenetics.Admixture (exists_driftModel)

/-- Lineage weights of the quartet tree rooted at the left internal node:
edges `(ea, eb, eint, ec, ed)`, populations `A=0, B=1` left, `C=2, D=3` right. -/
def wQuartet : Fin 4 → Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 1, 0, 1]]

/-- Tree example satisfying the split conclusion: internal length `3`,
`f4(A,B;C,D) = 0`, crossing permutations both `3`. -/
theorem quartet_split_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 5) (Fin 4)), M.weight = wQuartet ∧ M.len = ![1, 2, 3, 4, 5] ∧
        f4 μ M.freq 0 1 2 3 = 0 ∧ f4 μ M.freq 0 2 1 3 = 3 ∧ f4 μ M.freq 0 3 1 2 = 3 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wQuartet ![1, 2, 3, 4, 5] (by
    intro e
    fin_cases e <;> norm_num)
  refine ⟨Ω, hΩ, μ, hμ, M, hw, hl, ?_, ?_, ?_⟩ <;>
    · rw [M.f4_freq, hw, hl]
      norm_num [Fin.sum_univ_five, wQuartet]

/-- Zero internal branch: with internal length `0` all three f4 permutations
vanish in the same quartet. -/
theorem quartet_zero_internal_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 5) (Fin 4)), M.weight = wQuartet ∧ M.len = ![1, 2, 0, 4, 5] ∧
        f4 μ M.freq 0 1 2 3 = 0 ∧ f4 μ M.freq 0 2 1 3 = 0 ∧ f4 μ M.freq 0 3 1 2 = 0 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wQuartet ![1, 2, 0, 4, 5] (by
    intro e
    fin_cases e <;> norm_num)
  refine ⟨Ω, hΩ, μ, hμ, M, hw, hl, ?_, ?_, ?_⟩ <;>
    · rw [M.f4_freq, hw, hl]
      norm_num [Fin.sum_univ_five, wQuartet]

/-- Square example, binary loadings but not a tree: the f4 permutations are
`(1, 1, 0)`. In particular, with the split named `AB|CD` the crossing
permutations are not equal, so binary loadings alone do not give the
trichotomy's split conclusion; a tree hypothesis is essential. (The
four-point failure is `Admixture.not_fourPointCondition_squareF2` in Part 1.) -/
def wSquare : Fin 4 → Fin 2 → ℝ := ![![0, 0], ![1, 0], ![0, 1], ![1, 1]]

theorem square_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 2) (Fin 4)), M.weight = wSquare ∧ M.HasBinaryLoadings ∧
        f4 μ M.freq 0 1 2 3 = 1 ∧ f4 μ M.freq 0 2 1 3 = 1 ∧ f4 μ M.freq 0 3 1 2 = 0 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, hw, hl⟩ := exists_driftModel wSquare ![1, 1] (by
    intro e
    fin_cases e <;> norm_num)
  refine ⟨Ω, hΩ, μ, hμ, M, hw, ?_, ?_, ?_, ?_⟩
  · intro X e
    fin_cases X <;> fin_cases e <;> simp [hw, wSquare]
  · rw [M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_two, wSquare]
  · rw [M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_two, wSquare]
  · rw [M.f4_freq, hw, hl]
    norm_num [Fin.sum_univ_two, wSquare]

/-- Endpoint probe: a single population repeated four times has all pair sums
equal (`0`) and all f4 permutations zero. -/
example {Ω P : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {p : P → Ω → ℝ}
    (hp : ∀ X, MemLp (p X) 2 μ) (A : P) :
    f4 μ p A A A A = 0 ∧ f4 μ p A A A A = 0 :=
  ⟨by
    have h := (f4_eq_zero_of_pairSums_eq hp A A A A (by simp) (by simp)).1
    exact h, by simp [f4]⟩

end MathlibExtTest.Biology.PopulationGenetics.Admixture.FourPoint
