/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.EwensWatterson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tests for the Ewens–Watterson conditional law and homozygosity test

Samples of two genes (each number of alleles has a single allelic partition, so the
conditional law is a point mass), the cycle-type weights of four genes with two alleles
(`8 + 3 = 11 = |s(4, 2)|`), the law of the number of alleles, the homozygosity statistic,
the validity of the p-values, and the junk value at `θ = 0`.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.EwensWatterson

open MathlibExt.Biology.PopulationGenetics.Ewens

/-- The allelic partition `{1, 1}` of two genes (two distinct alleles). -/
def twoAlleles : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by simp

/-- The allelic partition `{2}` of two genes (one allele). -/
def oneAllele : Nat.Partition 2 := Nat.Partition.indiscrete 2

/-- The allelic partition `{3, 1}` of four genes. -/
def threeOne : Nat.Partition 4 where
  parts := {3, 1}
  parts_pos := by simp
  parts_sum := by simp

/-- The allelic partition `{2, 2}` of four genes. -/
def twoTwo : Nat.Partition 4 where
  parts := {2, 2}
  parts_pos := by simp
  parts_sum := by simp

/-- `w({2}) = 2! / (2 · 1!) = 1` (one transposition). -/
example : cycleTypeWeight oneAllele = 1 := by
  simp [cycleTypeWeight, oneAllele]

/-- `w({1, 1}) = 2! / (1² · 2!) = 1` (the identity). -/
example : cycleTypeWeight twoAlleles = 1 := by
  simp [cycleTypeWeight, twoAlleles, Multiset.count_cons]

/-- `w({3, 1}) = 4! / 3 = 8` (the 3-cycles of four letters). -/
example : cycleTypeWeight threeOne = 8 := by
  simp [cycleTypeWeight, threeOne, Multiset.count_cons, Nat.factorial]
  norm_num

/-- `w({2, 2}) = 4! / (2² · 2!) = 3` (the double transpositions). -/
example : cycleTypeWeight twoTwo = 3 := by
  simp [cycleTypeWeight, twoTwo, Multiset.count_cons, Nat.factorial]
  norm_num

/-- `8 + 3 = |s(4, 2)| = 11`, from the general theorem. -/
example : ∑ π : Nat.Partition 4 with π.parts.card = 2, cycleTypeWeight π = 11 := by
  rw [sum_cycleTypeWeight_eq_stirlingFirst]
  norm_num [Nat.stirlingFirst]

/-- The law of the number of alleles for two genes: `P(K = 1) = 1 / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) : numAllelesProb θ 2 1 = 1 / (θ + 1) := by
  rw [numAllelesProb_eq]
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [Nat.stirlingFirst, ascPochhammer_succ_eval]
  field_simp

/-- The conditional law given `K = 2` for two genes is a point mass on `{1, 1}`, for every
`θ > 0` (here from the Stirling form, `|s(2, 2)| = 1`). -/
example (θ : ℝ) (hθ : 0 < θ) : ewensCondProb θ twoAlleles = 1 := by
  rw [ewensCondProb_eq_stirlingFirst hθ]
  simp [cycleTypeWeight, twoAlleles, Multiset.count_cons, Nat.stirlingFirst]

/-- The conditional law does not depend on `θ`. -/
example (π : Nat.Partition 4) : ewensCondProb 1 π = ewensCondProb 7 π := by
  rw [ewensCondProb_eq one_pos, ewensCondProb_eq (by norm_num)]

/-- Watterson's statistic: one allele gives homozygosity `1`. -/
example : homozygosity oneAllele = 1 := by
  simp [homozygosity, oneAllele]

/-- Two distinct alleles in two genes give homozygosity `1 / 2`. -/
example : homozygosity twoAlleles = 1 / 2 := by
  simp [homozygosity, twoAlleles]
  norm_num

/-- The homozygosity tests in both tails are valid at level `0.05` for every `θ > 0`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    ∑ π : Nat.Partition 6 with condUpperPValue homozygosity π ≤ 0.05, ewensProb θ π ≤ 0.05 ∧
    ∑ π : Nat.Partition 6 with condUpperPValue (fun π => -homozygosity π) π ≤ 0.05,
      ewensProb θ π ≤ 0.05 :=
  ⟨sum_condUpperPValue_le hθ _ (by norm_num), sum_condUpperPValue_le hθ _ (by norm_num)⟩

/-- Outside the domain `θ > 0`: for `θ = 0` every Ewens probability of a nonempty sample is
the junk value `0`, and so is the conditional probability (`0 / 0`). -/
example : ewensCondProb 0 twoAlleles = 0 := by
  simp [ewensCondProb, ewensProb, ascPochhammer_succ_eval]

end MathlibExtTest.Biology.PopulationGenetics.EwensWatterson
