/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-!
# Tests for Λ-coalescent merger rates

Concrete measures `Λ` on `[0, 1]` (the model has no structure beyond a finite measure; these
are the non-vacuity witnesses): Kingman (`δ₀`), Bolthausen–Sznitman (uniform), a point mass
at `1/2`, and the zero measure. Small rate values, the consistency relation on concrete
numbers, the boundary cases outside `2 ≤ k ≤ b`, block-counting jump rates, and uniqueness
separating two measures.
-/

@[expose] public section

open MeasureTheory unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent

/-! ### Kingman: `Λ = δ₀` -/

/-- Kingman: a pair among three blocks merges at rate `1`. -/
example : mergerRate (Measure.dirac 0) 3 2 = 1 := by
  rw [mergerRate_dirac_zero]; norm_num

/-- Kingman: no triple mergers. -/
example : mergerRate (Measure.dirac 0) 3 3 = 0 := by
  rw [mergerRate_dirac_zero]; norm_num

/-- Kingman: four blocks, total rate `4.choose 2 = 6`. -/
example : totalMergerRate (Measure.dirac 0) 4 = 6 := by
  rw [totalMergerRate_dirac_zero]; norm_num [Nat.choose]

/-- Kingman block counting: from `3` blocks to `2` at rate `3`. -/
example : blockCountingGenerator (Measure.dirac 0) 4 3 2 = 3 := by
  simp [blockCountingGenerator, mergerRate_dirac_zero]

/-- Kingman block counting: no jump from `3` blocks straight to `1`. -/
example : blockCountingGenerator (Measure.dirac 0) 4 3 1 = 0 := by
  simp [blockCountingGenerator, mergerRate_dirac_zero]

/-- Kingman block counting: the diagonal entry at `3` blocks is `-3`. -/
example : blockCountingGenerator (Measure.dirac 0) 4 3 3 = -3 := by
  simp [blockCountingGenerator, totalMergerRate_dirac_zero, Nat.choose]

/-! ### Bolthausen–Sznitman: `Λ` uniform -/

/-- Bolthausen–Sznitman: `λ_{2,2} = 1`. -/
example : mergerRate volume 2 2 = 1 := by
  rw [mergerRate_volume le_rfl le_rfl]; norm_num

/-- Bolthausen–Sznitman: `λ_{3,2} = 1/2`. -/
example : mergerRate volume 3 2 = 1 / 2 := by
  rw [mergerRate_volume le_rfl (by norm_num)]; norm_num [Nat.factorial]

/-- Bolthausen–Sznitman: `λ_{3,3} = 1/2`. -/
example : mergerRate volume 3 3 = 1 / 2 := by
  rw [mergerRate_volume (by norm_num) le_rfl]; norm_num [Nat.factorial]

/-- Consistency on numbers: `λ_{2,2} = λ_{3,2} + λ_{3,3}`, i.e. `1 = 1/2 + 1/2`. -/
example : mergerRate volume 2 2 = mergerRate volume 3 2 + mergerRate volume 3 3 :=
  mergerRate_consistent volume le_rfl le_rfl

/-- Bolthausen–Sznitman: `λ_4 = 3`. -/
example : totalMergerRate volume 4 = 3 := by
  rw [totalMergerRate_volume (by norm_num)]; norm_num

/-- The Bolthausen–Sznitman block-counting generator is a rate matrix. -/
example : ProbabilityTheory.IsRateMatrix (blockCountingGenerator volume 5) :=
  isRateMatrix_blockCountingGenerator volume 5

/-! ### A point mass at `1/2` -/

/-- The point `1/2` of the unit interval. -/
noncomputable abbrev half : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `Λ = δ_{1/2}`: `λ_{3,3} = (1/2) ^ 1 (1/2) ^ 0 = 1/2`. -/
example : mergerRate (Measure.dirac half) 3 3 = 1 / 2 := by
  rw [mergerRate_of_le _ (by norm_num) le_rfl, integral_dirac]; norm_num

/-- `Λ = δ_{1/2}`: the pair rate is the total mass `1`. -/
example : mergerRate (Measure.dirac half) 2 2 = 1 := by
  rw [mergerRate_two_two]; simp

/-! ### Boundary cases and the zero measure -/

/-- Outside `2 ≤ k ≤ b` the rate is `0` (no junk value from natural subtraction). -/
example (Λ : Measure I) [IsFiniteMeasure Λ] (b : ℕ) : mergerRate Λ b 1 = 0 := by
  simp [mergerRate]

/-- A `3`-merger among `2` blocks does not exist: rate `0`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] : mergerRate Λ 2 3 = 0 := by
  simp [mergerRate]

/-- One block: no mergers, total rate `0`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] : totalMergerRate Λ 1 = 0 := by
  simp [totalMergerRate]

/-- The zero measure has all rates `0`. -/
example (b k : ℕ) : mergerRate (0 : Measure I) b k = 0 := by
  simp [mergerRate]

/-- The total merger rate is nondecreasing: `λ_3 ≤ λ_5`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] : totalMergerRate Λ 3 ≤ totalMergerRate Λ 5 :=
  totalMergerRate_mono Λ (by norm_num)

/-- `λ_3 = λ_2 + 2 λ_{3,2}`. -/
example (Λ : Measure I) [IsFiniteMeasure Λ] :
    totalMergerRate Λ 3 = totalMergerRate Λ 2 + 2 * mergerRate Λ 3 2 := by
  simpa using totalMergerRate_succ Λ 2

/-! ### Uniqueness -/

/-- Two measures with the same complete-merger rates coincide. -/
example (Λ Λ' : Measure I) [IsFiniteMeasure Λ] [IsFiniteMeasure Λ']
    (h : ∀ k, 2 ≤ k → mergerRate Λ k k = mergerRate Λ' k k) : Λ = Λ' :=
  eq_of_mergerRate_eq Λ Λ' h

/-- Kingman and Bolthausen–Sznitman are distinguished by `λ_{3,3}` (`0` versus `1/2`). -/
example : mergerRate (Measure.dirac 0) 3 3 ≠ mergerRate volume 3 3 := by
  rw [mergerRate_dirac_zero, mergerRate_volume (by norm_num) le_rfl]; norm_num [Nat.factorial]

#print axioms mergerRate_consistent
#print axioms totalMergerRate_eq
#print axioms eq_of_mergerRate_eq
#print axioms mergerRate_volume

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
