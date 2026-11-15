/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaSFS

/-!
# Tests for the expected site frequency spectrum under Λ-coalescents

Merging on concrete block-size lists; boundary cases (no blocks, one block, `Λ = 0`) and the
two-copy spectrum for every `Λ`, computed from the definitions; cross-checks between the
general three-copy formula and the Kingman (`δ₀`) and star (`δ₁`) theorems; the
Bolthausen–Sznitman (uniform `Λ`) spectrum for three copies; and the non-vacuity of the
`Λ ≠ 0` hypothesis.
-/

@[expose] public section

open MeasureTheory Finset unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSFS

open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaSFS

/-! ### Merging blocks -/

/-- Merging the first and third of three blocks. -/
example : mergeSet [1, 2, 3] {0, 2} = [2, 4] := by decide

/-- A triple merger among four blocks. -/
example : mergeSet [1, 1, 1, 1] {0, 1, 3} = [1, 3] := by decide

/-- All blocks merge into one. -/
example : mergeSet [1, 2, 3] {0, 1, 2} = [6] := by decide

/-- Merging two of four blocks leaves three. -/
example : (mergeSet [1, 2, 3, 4] {1, 3}).length = 3 := by decide

/-- For a pair, `mergeSet` is the Kingman file's `mergeBlocks`, computed. -/
example : mergeSet [5, 6, 7] {0, 2} =
    MathlibExt.Biology.PopulationGenetics.Coalescent.SiteFrequencySpectrum.mergeBlocks
      [5, 6, 7] 0 2 := by decide

/-! ### Boundary cases, from the definitions -/

/-- No blocks: no branches. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (i : ℕ) : expectedLength Λ i [] = 0 := by
  simp [expectedLength]

/-- One block: no branches (the holding rate `λ_1` is `0`). -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (i m : ℕ) : expectedLength Λ i [m] = 0 := by
  simp [expectedLength, holdingCount, totalMergerRate]

/-- `Λ = 0`: no merger ever happens, every state is absorbing. -/
example (g : List ℕ → ℝ) (b : List ℕ) : jumpStep (0 : Measure I) g b = g b := by
  simp [jumpStep, totalMergerRate, mergerRate]

/-- Two copies, any `Λ`: the two singleton branches have total expected length
`2 / Λ [0, 1]`, computed from the definitions (both sides are `0` when `Λ = 0`). -/
example (Λ : Measure I) [IsFiniteMeasure Λ] :
    expectedLength Λ 1 [1, 1] = 2 / Λ.real Set.univ := by
  have h2 : totalMergerRate Λ 2 = Λ.real Set.univ := by
    simp [totalMergerRate, mergerRate_two_two]
  have h1 : totalMergerRate Λ 1 = 0 := by simp [totalMergerRate]
  have hm : mergeSet [1, 1] {0, 1} = [2] := by decide
  rw [expectedLength, show ([1, 1] : List ℕ).length = 2 from rfl, sum_range_succ, sum_range_one,
    Function.iterate_zero_apply, Function.iterate_one]
  by_cases h0 : Λ.real Set.univ = 0
  · simp [jumpStep, holdingCount, h2, h0]
  · rw [jumpStep, show ([1, 1] : List ℕ).length = 2 from rfl, h2, ite_eq_right h0,
      show (range 2).powerset = {∅, {0}, {1}, {0, 1}} by decide,
      sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton, hm]
    simp [holdingCount, h1, h2, mergerRate]

/-! ### Cross-checks: Kingman (`δ₀`) and star (`δ₁`) -/

private lemma dirac_ne_zero (x : I) : (Measure.dirac x : Measure I) ≠ 0 :=
  (Measure.dirac.isProbabilityMeasure).ne_zero

private lemma real_dirac_univ (x : I) : (Measure.dirac x : Measure I).real Set.univ = 1 := by
  simp

/-- Kingman, three copies, through the general three-copy formula: `E L_1 = 2`. -/
example : expectedLength (Measure.dirac 0) 1 [1, 1, 1] = 2 := by
  rw [expectedLength_three_one _ (dirac_ne_zero 0), real_dirac_univ, totalMergerRate_dirac_zero,
    mergerRate_dirac_zero]
  norm_num [Nat.choose]

/-- The same value through the Kingman theorem: `E L_1 = 2 / 1`. -/
example : expectedLength (Measure.dirac 0) 1 [1, 1, 1] = 2 := by
  have := expectedLength_dirac_zero (n := 3) (i := 1) le_rfl (by norm_num)
  norm_num at this
  exact this

/-- Kingman, three copies, through the general formula: `E L_2 = 1 = 2 / 2`. -/
example : expectedLength (Measure.dirac 0) 2 [1, 1, 1] = 1 := by
  rw [expectedLength_three_two _ (dirac_ne_zero 0), real_dirac_univ, totalMergerRate_dirac_zero,
    mergerRate_dirac_zero]
  norm_num [Nat.choose]

/-- Star coalescent, three copies, through the general formula: `E L_1 = 3 = n`. -/
example : expectedLength (Measure.dirac 1) 1 [1, 1, 1] = 3 := by
  rw [expectedLength_three_one _ (dirac_ne_zero 1), totalMergerRate_dirac_one (by norm_num),
    mergerRate_dirac_one (by norm_num)]
  norm_num

/-- Star coalescent through its own theorem: `E L_1 = 3`, `E L_2 = 0`. -/
example : expectedLength (Measure.dirac 1) 1 [1, 1, 1] = 3 ∧
    expectedLength (Measure.dirac 1) 2 [1, 1, 1] = 0 := by
  have h1 := expectedLength_dirac_one (n := 3) (by norm_num) 1
  have h2 := expectedLength_dirac_one (n := 3) (by norm_num) 2
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- The spectrum depends on `Λ`: with three copies, Kingman has doubleton branches of
expected length `1`, the star coalescent none. -/
example : expectedLength (Measure.dirac 0) 2 [1, 1, 1] ≠
    expectedLength (Measure.dirac 1) 2 [1, 1, 1] := by
  rw [expectedLength_three_two _ (dirac_ne_zero 0), expectedLength_three_two _ (dirac_ne_zero 1),
    real_dirac_univ, real_dirac_univ, totalMergerRate_dirac_zero, mergerRate_dirac_zero,
    totalMergerRate_dirac_one (by norm_num), mergerRate_dirac_one (by norm_num)]
  norm_num [Nat.choose]

/-- Fu's spectrum for Kingman: `E ξ_3 = θ / 3` with four copies. -/
example (θ : ℝ) : expectedSFS (Measure.dirac 0) θ 4 3 = θ / 3 := by
  rw [expectedSFS_dirac_zero θ (by norm_num) (by norm_num)]
  norm_num

/-- Star coalescent with four copies: `E ξ_1 = 2 θ`, `E ξ_3 = 0`. -/
example (θ : ℝ) : expectedSFS (Measure.dirac 1) θ 4 1 = 2 * θ ∧
    expectedSFS (Measure.dirac 1) θ 4 3 = 0 := by
  rw [expectedSFS_dirac_one θ (by norm_num), expectedSFS_dirac_one θ (by norm_num)]
  constructor
  · norm_num; ring
  · norm_num

/-! ### Bolthausen–Sznitman: `Λ` uniform -/

private lemma volume_ne_zero : (volume : Measure I) ≠ 0 := NeZero.ne _

/-- Bolthausen–Sznitman, three copies: `λ_3 = 2`, `λ_{3,2} = 1/2`, `λ_2 = 1`, so
`E L_1 = 3/2 + 3/4 = 9/4`. -/
example : expectedLength volume 1 [1, 1, 1] = 9 / 4 := by
  rw [expectedLength_three_one _ volume_ne_zero, totalMergerRate_volume (by norm_num),
    mergerRate_volume le_rfl (by norm_num)]
  norm_num [Nat.factorial]

/-- Bolthausen–Sznitman, three copies: `E L_2 = 3/4`. -/
example : expectedLength volume 2 [1, 1, 1] = 3 / 4 := by
  rw [expectedLength_three_two _ volume_ne_zero, totalMergerRate_volume (by norm_num),
    mergerRate_volume le_rfl (by norm_num)]
  norm_num [Nat.factorial]

/-! ### The jump chain -/

/-- The transition probabilities of the Bolthausen–Sznitman jump chain sum to `1`. -/
example (b : List ℕ) : jumpStep volume (fun _ => (1 : ℝ)) b = 1 := jumpStep_const volume 1 b

/-- Kingman block counting: from three blocks the chain always moves to two. -/
example (h : ℕ → ℝ) : jumpStep (Measure.dirac 0) (fun s => h s.length) [1, 1, 1] = h 2 := by
  rw [jumpStep_comp_length _ h (by rw [totalMergerRate_dirac_zero]; norm_num [Nat.choose])]
  simp only [List.length_cons, List.length_nil, totalMergerRate_dirac_zero,
    mergerRate_dirac_zero]
  rw [show Icc 2 (0 + 1 + 1 + 1) = {2, 3} by decide, sum_pair (by norm_num)]
  norm_num [Nat.choose]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaSFS
