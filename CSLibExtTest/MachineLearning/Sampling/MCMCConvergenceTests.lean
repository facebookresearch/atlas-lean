/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MCMCConvergence

@[expose] public section

/-!
# Tests for the convergence of Metropolis–Hastings and Gibbs samplers
-/

set_option autoImplicit false

open Matrix Cslib.MachineLearning.Sampling MathlibExt.Probability.MarkovMixing
open scoped ENNReal NNReal

namespace CSLibExtTest.MachineLearning.Sampling.MCMCConvergence

/-- The uniform law on bits. -/
noncomputable def unifBool : PMF Bool :=
  PMF.ofFintype (fun _ => 2⁻¹) (by simp [ENNReal.mul_inv_cancel])

/-- The uniform target on bits has full support. -/
theorem unifBool_pos (x : Bool) : unifBool x ≠ 0 := by
  simp [unifBool]

/-- The uniform independence proposal on bits. -/
noncomputable def Q₀ : Bool → PMF Bool := fun _ => unifBool

theorem Q₀_symm (x y : Bool) (_ : Q₀ x y ≠ 0) : Q₀ y x ≠ 0 := by
  simp [Q₀, unifBool]

theorem Q₀_isPrimitive : (Matrix.of fun x y => (Q₀ x y).toReal).IsPrimitive :=
  ⟨fun _ _ => ENNReal.toReal_nonneg, 1, one_pos, fun _ _ => by
    simp [Q₀, unifBool]⟩

/-- Non-vacuity: Metropolis–Hastings with the uniform proposal converges to the uniform target. -/
example : ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Bool),
    tvDist (fun y => (mhMatrix (unifBool) Q₀ ^ n) x y)
      (fun y => (unifBool y).toReal) ≤ C * ρ ^ n :=
  exists_tvDist_mhMatrix_pow_le unifBool_pos Q₀_symm Q₀_isPrimitive

/-- The Metropolis–Hastings matrix is stochastic for any target and proposal. -/
example (π : PMF Bool) (Q : Bool → PMF Bool) : mhMatrix π Q ∈ rowStochastic ℝ Bool :=
  mhMatrix_mem_rowStochastic π Q

/-- The uniform law on pairs of bits. -/
noncomputable def unifPair : PMF (Fin 2 → Bool) :=
  PMF.ofFintype (fun _ ↦ ((1 / 4 : ℝ≥0) : ℝ≥0∞)) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul, ← ENNReal.coe_one, ENNReal.coe_inj,
      ← NNReal.coe_inj]
    push_cast
    norm_num)

/-- The uniform target on pairs of bits has full support. -/
theorem unifPair_pos (x : Fin 2 → Bool) : unifPair x ≠ 0 := by
  simp [unifPair]

/-- Non-vacuity: the systematic-scan Gibbs sampler updating coordinates `0` then `1` converges to
the uniform target on pairs of bits. -/
example : ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Fin 2 → Bool),
    tvDist (fun y => (gibbsSweepMatrix (unifPair) unifPair_pos
        [0, 1] ^ n) x y) (fun y => (unifPair y).toReal) ≤
      C * ρ ^ n :=
  exists_tvDist_gibbsSweepMatrix_pow_le _ unifPair_pos (by decide)

/-- Boundary case: the hypothesis that the sweep visits every coordinate is needed. The empty
sweep is the identity kernel, which never leaves its starting state (and is not primitive on
the four states). -/
example (x : Fin 2 → Bool) :
    gibbsSweepMatrix (unifPair) unifPair_pos [] x x = 1 := by
  simp [gibbsSweepMatrix, gibbsSweep, ProbabilityTheory.Kernel.id_apply]

end CSLibExtTest.MachineLearning.Sampling.MCMCConvergence
