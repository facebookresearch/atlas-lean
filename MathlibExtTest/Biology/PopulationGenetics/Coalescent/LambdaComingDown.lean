/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaComingDown

/-!
# Tests for the block-count drift

The examples check the Kingman value through the generator itself, the absorbing
endpoints, the Bolthausen–Sznitman separation of the drift from the total merger rate,
and the zero measure.
-/

@[expose] public section

open MeasureTheory Finset unitInterval Matrix
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaComingDown

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaComingDown

variable {Λ : Measure I} [IsFiniteMeasure Λ]

/-! ### Extra checks: acceptance, endpoints, non-vacuity -/

-- the closed form of the kernel, stated through the public definition
example (x : ℝ) (b : ℕ) : x ^ 2 * driftKernel b x = b * x - 1 + (1 - x) ^ b :=
  sq_mul_driftKernel x b

-- acceptance 1: Kingman, through the generator itself (`Λ = δ₀`, from 5 blocks)
example : (blockCountingGenerator (Measure.dirac (0 : I)) 5 *ᵥ fun j => ((j : ℕ) : ℝ)) 5 = -10 := by
  rw [blockCountingGenerator_mulVec_natCast, blockDrift_dirac_zero]
  norm_num [Nat.choose]

-- acceptance 2: the block-counting generator applied to `f(b) = b` is `-γ_b`, for every finite Λ
example (n : ℕ) (b : Fin (n + 1)) :
    (blockCountingGenerator Λ n *ᵥ fun j => ((j : ℕ) : ℝ)) b = -blockDrift Λ b :=
  blockCountingGenerator_mulVec_natCast Λ n b

-- endpoints: no drift from 0 or 1 block (absorbing states); two blocks drift at the pair rate
example : blockDrift Λ 0 = 0 := by simp [blockDrift]
example : blockDrift Λ 1 = 0 := by simp [blockDrift]
example : blockDrift Λ 2 = Λ.real Set.univ := by
  simp [blockDrift, mergerRate_two_two]
  norm_num

-- γ_b ≥ λ_b (each merger removes at least one block): Bolthausen–Sznitman separates them
example : blockDrift volume 3 = 5 / 2 := by
  rw [blockDrift_volume, show (Icc 2 3 : Finset ℕ) = {2, 3} by decide]
  norm_num
example : totalMergerRate volume 3 = 2 := by
  rw [totalMergerRate_volume (by norm_num)]; norm_num

-- the zero measure gives no drift (degenerate boundary)
example (b : ℕ) : blockDrift (0 : Measure I) b = 0 := by
  simp [blockDrift, mergerRate]

#print axioms sq_mul_driftKernel
#print axioms blockDrift_eq_integral
#print axioms blockDrift_eq
#print axioms blockDrift_mono
#print axioms blockDrift_nonneg
#print axioms blockDrift_dirac_zero
#print axioms blockDrift_volume
#print axioms blockCountingGenerator_mulVec_natCast

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.LambdaComingDown
