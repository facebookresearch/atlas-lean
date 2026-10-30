/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LocalDeMoivreLaplace

@[expose] public section

open ProbabilityTheory Filter Topology Asymptotics

namespace MathlibExtTest.Probability.LocalDeMoivreLaplace

/-- The binomial point mass at the centre of `n = 2`: `C(2, 1) / 2² = 1 / 2`. -/
theorem binomProbHalf_two_one : binomProbHalf 2 1 = 1 / 2 := by
  norm_num [binomProbHalf]

/-- `C(4, 2) / 2⁴ = 6 / 16 = 3 / 8`. -/
theorem binomProbHalf_four_two : binomProbHalf 4 2 = 3 / 8 := by
  have h : Nat.choose 4 2 = 6 := by decide
  rw [binomProbHalf, h]
  norm_num

/-- At `x = 0` the lattice index is `⌊n / 2⌋`; in particular `localDMLIndex 0 10 = 5`. -/
theorem localDMLIndex_zero_ten : localDMLIndex 0 10 = 5 := by
  norm_num [localDMLIndex]

/-- The Gaussian approximation is positive for `n > 0`. -/
theorem gaussianApproxHalf_pos {n k : ℕ} (hn : 0 < n) :
    0 < gaussianApproxHalf n k := by
  unfold gaussianApproxHalf
  exact mul_pos
    (Real.sqrt_pos.mpr (div_pos (by norm_num) (mul_pos Real.pi_pos (by exact_mod_cast hn))))
    (Real.exp_pos _)

/-- At `n = 2, k = 1` the Gaussian approximation is `√(2 / (π · 2))`, since the
exponent `(k - n / 2)² / (n / 2)` vanishes there. -/
theorem gaussianApproxHalf_two_one :
    gaussianApproxHalf 2 1 = Real.sqrt (2 / (Real.pi * 2)) := by
  simp [gaussianApproxHalf]

/-- The local De Moivre–Laplace theorem at `x = 0` (the central case): the ratio
of the binomial point mass to its Gaussian approximation along the central
lattice sequence tends to `1`. -/
theorem local_deMoivreLaplace_half_zero :
    Tendsto (fun n => binomProbHalf n (localDMLIndex 0 n) /
      gaussianApproxHalf n (localDMLIndex 0 n)) atTop (𝓝 1) :=
  local_deMoivreLaplace_half 0

/-- The asymptotic-equivalence form at `x = 0`. -/
theorem binomProbHalf_isEquivalent_gaussianApproxHalf_zero :
    (fun n => binomProbHalf n (localDMLIndex 0 n)) ~[atTop]
      (fun n => gaussianApproxHalf n (localDMLIndex 0 n)) :=
  binomProbHalf_isEquivalent_gaussianApproxHalf 0

/-- The canonical rounded sequence also converges to the Gaussian expression at its fixed
limit, rather than only to the moving approximation. -/
theorem canonical_fixed_gaussian :
    (fun n => binomProbHalf n (localDMLIndex 0 n)) ~[atTop]
      (fun n => Real.sqrt (2 / (Real.pi * (n : ℝ)))) := by
  simpa using binomProbHalf_isEquivalent_fixedGaussian tendsto_id
    (localDMLIndex_standardized_tendsto 0)

/-- The noncanonical displacement `kₙ = 1` has scaled displacement tending to zero; its
success index `n + 1` is a valid lattice point for every positive `n`. -/
theorem noncanonical_one_fixed_gaussian :
    (fun n : ℕ => binomProbHalf (2 * n) (n + 1)) ~[atTop]
      (fun n => (Real.sqrt (Real.pi * (n : ℝ)))⁻¹) := by
  have hcount : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hscale : Tendsto (fun n : ℕ => 2 * ((1 : ℤ) : ℝ) /
      Real.sqrt (2 * (n : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_sqrt_atTop.comp hcount).const_div_atTop (2 : ℝ)
  simpa using local_deMoivreLaplace_half_of_tendsto hscale

end MathlibExtTest.Probability.LocalDeMoivreLaplace

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms ProbabilityTheory.local_deMoivreLaplace_half
#print axioms ProbabilityTheory.binomProbHalf_isEquivalent_gaussianApproxHalf
#print axioms MathlibExtTest.Probability.LocalDeMoivreLaplace.local_deMoivreLaplace_half_zero
