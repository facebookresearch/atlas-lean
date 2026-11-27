/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBound
import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis

open scoped lp
open InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis
open MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

namespace MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted

local notation "H" => ℓ²(ℕ, ℝ)

private instance separableL2 : TopologicalSpace.SeparableSpace H :=
  separableSpace_of_countable_hilbertBasis (default : HilbertBasis ℕ ℝ H)

private theorem infiniteDimensionalL2 : ¬ FiniteDimensional ℝ H := by
  intro h
  let b : HilbertBasis ℕ ℝ H := default
  exact Module.Finite.not_linearIndependent_of_infinite b b.orthonormal.linearIndependent

/-- At rank zero the operator norm forces the Hilbert–Schmidt norm to vanish. -/
example (b : HilbertBasis ℕ ℝ H) : hsENNNorm (0 : H →L[ℝ] H) b = 0 := by
  have : FiniteDimensional ℝ (H ⧸ (0 : H →L[ℝ] H).ker) := by
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.ker_zero]
    infer_instance
  obtain ⟨C, _, hC⟩ := exists_hsNorm_le_mul_opNorm_of_finiteDimensional_quotient_ker
  simpa using hC H infiniteDimensionalL2 0 b

/-- The projection onto any unit vector has a finite Hilbert–Schmidt norm in every basis. -/
example (u : H) (hu : ‖u‖ = 1) (b : HilbertBasis ℕ ℝ H) : hsENNNorm (rankOne ℝ u u) b < ⊤ := by
  let T := rankOne ℝ u u
  have hu₀ : u ≠ 0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  have hrank : Module.rank ℝ T.range = 1 := rank_rankOne hu₀ hu₀
  have : FiniteDimensional ℝ T.range :=
    Module.finite_of_finrank_eq_succ (Module.rank_eq_one_iff_finrank_eq_one.mp hrank)
  have : FiniteDimensional ℝ (H ⧸ T.ker) := T.toLinearMap.quotKerEquivRange.symm.finiteDimensional
  obtain ⟨C, _, hC⟩ := exists_hsNorm_le_mul_opNorm_of_finiteDimensional_quotient_ker
  exact (hC H infiniteDimensionalL2 T b).trans_lt ENNReal.ofReal_lt_top

end MathlibExt.Analysis.OperatorTheory.HilbertSchmidtFiniteRankBoundWanted
