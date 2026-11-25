/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperharmonicEulerSums

open MetaMathlibExt

-- The two singleton subsets contribute r and r + 1.
example (r : ℂ) : generalizedHyperharmonic 2 1 r = (2 * r + 1) / 2 := by
  simp [generalizedHyperharmonic, Finset.powersetCard_one, Finset.sum_range_succ,
    Nat.factorial_succ]
  ring

-- At depth zero and order zero only the constant coefficient survives.
private lemma zero_order (n : ℕ) :
    generalizedHyperharmonic n 0 0 = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Finset.powersetCard_self (Finset.range (n + 1))
    rw [Finset.card_range] at h
    simp [generalizedHyperharmonic, h, Finset.prod_range_succ']

-- Duality evaluates the depth-one sum by reducing it to a single nonzero term.
example : hyperharmonicEulerSum 1 0 1 1 = 1 := by
  have h := (hyperharmonicEulerSum_duality 1 0 0 0 (by norm_num) (by norm_num)).2.2
  simpa [hyperharmonicEulerSum, zero_order, ite_div] using h

-- The shift 1 - t can vanish when the starting index is positive.
example : Summable (fun n : ℕ => generalizedHyperharmonic (n + 1) 1 0 / (n + 1 : ℂ)) := by
  simpa using (hyperharmonicEulerSum_duality 1 0 0 1 (by norm_num) (by norm_num)).1

-- Choosing both odd harmonic factors leaves a single product.
example : oddMultipleHarmonic 2 2 = 4 / 3 := by
  have h := Finset.powersetCard_self (Finset.Icc 1 2)
  norm_num at h
  norm_num [oddMultipleHarmonic, h, Finset.prod_Icc_succ_top]

example : (Real.log 2 : ℂ) * riemannZeta 3 ∈ eulerSumPeriodAlgebra := by
  apply eulerSumPeriodAlgebra.mul_mem generators_mem_eulerSumPeriodAlgebra.1
  simpa using generators_mem_eulerSumPeriodAlgebra.2.2 0
