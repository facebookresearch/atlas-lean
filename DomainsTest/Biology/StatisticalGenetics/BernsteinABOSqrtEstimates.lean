/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates
import Mathlib.Tactic.NormNum

/-!
# Tests for Bernstein's square-root estimates

At the concrete allele frequencies `p = 1/4`, `q = 1/4`, `r = 1/2`, the phenotype frequencies
are `O = 1/4`, `A = B = 5/16` and `AB = 1/8`, and the square-root estimates recover the allele
frequencies. At the boundary `p = 1`, `q = r = 0`, the three estimates evaluate to `0`, `1`
and `0`, summing to `1`.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.BernsteinABOWanted

namespace DomainsTest.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates

/-- The phenotype frequencies at `p = 1/4`, `q = 1/4`, `r = 1/2`. -/
example : freqO (1 / 4 : ℝ) (1 / 4) (1 / 2) = 1 / 4 ∧
    freqA (1 / 4 : ℝ) (1 / 4) (1 / 2) = 5 / 16 ∧
    freqB (1 / 4 : ℝ) (1 / 4) (1 / 2) = 5 / 16 ∧
    freqAB (1 / 4 : ℝ) (1 / 4) (1 / 2) = 1 / 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [freqO, freqA, freqB, freqAB]

/-- At `p = 1/4`, `q = 1/4`, `r = 1/2`, the estimates recover the allele frequencies. -/
example : Real.sqrt (freqO (1 / 4 : ℝ) (1 / 4) (1 / 2)) = 1 / 2 ∧
    1 - Real.sqrt (freqO (1 / 4 : ℝ) (1 / 4) (1 / 2) +
      freqB (1 / 4 : ℝ) (1 / 4) (1 / 2)) = 1 / 4 ∧
    1 - Real.sqrt (freqO (1 / 4 : ℝ) (1 / 4) (1 / 2) +
      freqA (1 / 4 : ℝ) (1 / 4) (1 / 2)) = 1 / 4 := by
  have h := sqrt_estimates (1 / 4 : ℝ) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- At the boundary `p = 1`, `q = r = 0`, the three estimates evaluate to `0`, `1` and `0`. -/
example : Real.sqrt (freqO (1 : ℝ) 0 0) = 0 ∧
    1 - Real.sqrt (freqO (1 : ℝ) 0 0 + freqB (1 : ℝ) 0 0) = 1 ∧
    1 - Real.sqrt (freqO (1 : ℝ) 0 0 + freqA (1 : ℝ) 0 0) = 0 ∧
    Real.sqrt (freqO (1 : ℝ) 0 0) + (1 - Real.sqrt (freqO (1 : ℝ) 0 0 +
      freqB (1 : ℝ) 0 0)) + (1 - Real.sqrt (freqO (1 : ℝ) 0 0 + freqA (1 : ℝ) 0 0)) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [freqO, freqA, freqB, Real.sqrt_zero, Real.sqrt_one]

end DomainsTest.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates
