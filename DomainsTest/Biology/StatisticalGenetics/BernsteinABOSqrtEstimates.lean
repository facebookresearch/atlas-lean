/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Bernstein's square-root estimates

At the concrete allele frequencies `p = 1/4`, `q = 1/4`, `r = 1/2`, the phenotype frequencies
are `O = 1/4`, `A = B = 5/16` and `AB = 1/8`, and the square-root estimates recover the allele
frequencies. At the boundary `p = 1`, `q = r = 0`, the three estimates evaluate to `0`, `1`
and `0`, summing to `1`. For the two-locus comparison, the test at `p = q = 1/2`, `r = 0`
checks the strict inequality independently; the example at `p = q = 1/4`, `r = 1/2`
applies the public theorem.
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

/-- **Strict gap with no $O$ allele.** At $p=q=1/2$ and $r=0$, the product of the two
antigen frequencies exceeds the $AB$ frequency. -/
example :
    freqAB (1 / 2) (1 / 2) 0 <
      (freqA (1 / 2) (1 / 2) 0 + freqAB (1 / 2) (1 / 2) 0) *
        (freqB (1 / 2) (1 / 2) 0 + freqAB (1 / 2) (1 / 2) 0) := by
  obtain ⟨htotal, hO, hB, hA, _⟩ :=
    sqrt_estimates (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hO' := Real.sqrt_eq_zero'.mp hO
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hquarter : (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
  have hB' : freqO (1 / 2) (1 / 2) 0 + freqB (1 / 2) (1 / 2) 0 = 1 / 4 := by
    rw [hquarter]
    exact ((Real.sqrt_eq_iff_mul_self_eq_of_pos hhalf).mp (by linarith only [hB])).symm
  have hA' : freqO (1 / 2) (1 / 2) 0 + freqA (1 / 2) (1 / 2) 0 = 1 / 4 := by
    rw [hquarter]
    exact ((Real.sqrt_eq_iff_mul_self_eq_of_pos hhalf).mp (by linarith only [hA])).symm
  have hAAB : freqA (1 / 2) (1 / 2) 0 + freqAB (1 / 2) (1 / 2) 0 = 3 / 4 := by
    linarith only [htotal, hB']
  have hBAB : freqB (1 / 2) (1 / 2) 0 + freqAB (1 / 2) (1 / 2) 0 = 3 / 4 := by
    linarith only [htotal, hA']
  rw [hAAB, hBAB]
  linarith only [htotal, hA', hB', hO']

/-- **Strict gap with all three alleles.** At $p=q=1/4$ and $r=1/2$, the product of the two
antigen frequencies exceeds the $AB$ frequency. -/
example :
    freqAB (1 / 4) (1 / 4) (1 / 2) <
      (freqA (1 / 4) (1 / 4) (1 / 2) + freqAB (1 / 4) (1 / 4) (1 / 2)) *
        (freqB (1 / 4) (1 / 4) (1 / 2) + freqAB (1 / 4) (1 / 4) (1 / 2)) := by
  exact tripleAllele_violates_twoLocus (1 / 4) (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end DomainsTest.Biology.StatisticalGenetics.BernsteinABOSqrtEstimates
