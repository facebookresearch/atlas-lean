/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.PopulationStructure.WeightedLDFFT
public import Mathlib.Tactic.NormNum

/-!
# ALDER Fourier-transform weighted LD tests

Three SNPs in cells `0, 1, 1` (so `K = 2`), per-SNP values `1, 2, 3`.

* Brute-force pair sums by direct evaluation: offset `1` gives `1·2 + 1·3 = 5`; offset `0`
  includes the diagonal and gives `1 + (2 + 3)^2 = 26`; cell totals `U = (1, 5)`.
* Binning (`pairSum_eq_sum_cellSum`) reproduces both values.
* Transform instances: with transform length `N = 3 = 2K - 1` (the smallest allowed),
  `autocorrDFT` returns `5` and `26`, and the pair counts `2` and `5`.
* Weighted LD: two individuals with genotypes `(0, 1, 2)` and `(2, 1, 0)` and unit weights;
  the transform algorithm equals the brute-force sum, which is evaluated directly as `-2`.
-/

@[expose] public section

open Cslib.Bioinformatics.PopulationStructure.WeightedLDFFT

namespace CSLibExtTest.Bioinformatics.PopulationStructure.WeightedLDFFT

/-- Grid cells of three SNPs: `0, 1, 1`. -/
def cells : Fin 3 → ℕ := ![0, 1, 1]

/-- Per-SNP values `1, 2, 3`. -/
noncomputable def u : Fin 3 → ℝ := ![1, 2, 3]

theorem cells_lt (x : Fin 3) : cells x < 2 := by
  fin_cases x <;> simp [cells]

/-- Offset `1`: only the pairs `(0, 1)` and `(0, 2)`, giving `2 + 3 = 5`. -/
theorem pairSum_one : pairSum cells u u 1 = 5 := by
  simp [pairSum, cells, u, Fin.sum_univ_three]
  norm_num

/-- Offset `0` includes the diagonal: `1 + (2 + 3)^2 = 26`. -/
theorem pairSum_zero : pairSum cells u u 0 = 26 := by
  simp [pairSum, cells, u, Fin.sum_univ_three]
  norm_num

/-- The cell totals are `U 0 = 1`, `U 1 = 5`, and `0` beyond. -/
example : cellSum cells u 0 = 1 ∧ cellSum cells u 1 = 5 ∧ cellSum cells u 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [cellSum, Finset.sum_filter, Fin.sum_univ_three] <;>
    norm_num [cells, u]

/-- Binning reproduces the brute-force value at offset `1`. -/
example : ∑ k ∈ Finset.range 2, cellSum cells u k * cellSum cells u (k + 1) = 5 := by
  rw [← pairSum_eq_sum_cellSum cells cells_lt, pairSum_one]

/-- The transform computation at offset `1`, with the minimal transform length `N = 3`. -/
example : autocorrDFT 3 (cellSum cells u) 1 = 5 := by
  rw [autocorrDFT_eq (K := 2) (fun k hk => ?_) (by norm_num) (by norm_num),
    ← pairSum_eq_sum_cellSum cells cells_lt, pairSum_one]
  · norm_num
  · simp only [cellSum]
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    exact absurd hx.2 (by have := cells_lt x; omega)

/-- The transform computation at offset `0`. -/
example : autocorrDFT 3 (cellSum cells u) 0 = 26 := by
  rw [autocorrDFT_eq (K := 2) (fun k hk => ?_) (by norm_num) (by norm_num),
    ← pairSum_eq_sum_cellSum cells cells_lt, pairSum_zero]
  · norm_num
  · simp only [cellSum]
    refine Finset.sum_eq_zero fun x hx => ?_
    simp only [Finset.mem_filter] at hx
    exact absurd hx.2 (by have := cells_lt x; omega)

/-- Pair counts: `2` pairs at offset `1`, `5` at offset `0` (direct evaluation). -/
example : pairCount cells 1 = 2 ∧ pairCount cells 0 = 5 := by
  constructor <;> decide

/-- The pair count through the transform. -/
example : autocorrDFT 3 (cellSum cells fun _ => 1) 1 = 2 := by
  rw [autocorrDFT_cellCount (N := 3) (K := 2) cells cells_lt (by norm_num) (by norm_num)]
  have : pairCount cells 1 = 2 := by decide
  rw [this]
  norm_num

/-! ### Weighted LD -/

/-- Two individuals with genotypes `(0, 1, 2)` and `(2, 1, 0)`. -/
noncomputable def geno : Fin 2 → Fin 3 → ℝ := ![![0, 1, 2], ![2, 1, 0]]

/-- Brute force at offset `1` with unit weights: the means are `(1, 1, 1)`, so
`ẑ(0, 1) = 0` and `ẑ(0, 2) = ((-1)(1) + (1)(-1)) / 1 = -2`, and the sum is `-2`. -/
theorem brute_one : bruteWeightedLD cells geno (fun _ => 1) 1 = -2 := by
  simp [bruteWeightedLD, sampleCov, meanGeno, cells, geno, Fin.sum_univ_three,
    Fin.sum_univ_two]
  norm_num

/-- The transform algorithm returns the brute-force value. -/
example : dftWeightedLD cells geno (fun _ => 1) 3 1 = -2 := by
  rw [dftWeightedLD_eq_bruteWeightedLD (K := 2) cells geno _ cells_lt (by norm_num)
    (by norm_num), brute_one]
  norm_num

end CSLibExtTest.Bioinformatics.PopulationStructure.WeightedLDFFT
