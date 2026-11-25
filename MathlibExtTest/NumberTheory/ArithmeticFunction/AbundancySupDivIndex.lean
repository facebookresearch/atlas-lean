/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.AbundancySupDivIndex

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted MetaMathlibExt

-- For an odd prime, erasing the distinguished prime leaves an empty product.
example (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    abundancySup p / abundancyIndex p ≤ (p : ℚ) ^ 2 / ((p : ℚ) ^ 2 - 1) := by
  simpa [hp.primeFactors] using abundancySup_div_abundancyIndex_le_of_single_odd_exponent
    p p hodd (by simp [hp.primeFactors]) (by simp [hp.factorization_self])
    (by simp [hp.primeFactors])

-- Both local bounds are sharp for 45 = 3² · 5.
example : abundancySup 45 / abundancyIndex 45 =
    (5 : ℚ) ^ 2 / (5 ^ 2 - 1) * (3 ^ 3 / (3 ^ 3 - 1)) := by
  have hrest : (45 : ℕ).primeFactors.erase 5 = {3} := by decide +kernel
  apply le_antisymm
  · simpa only [hrest, Finset.prod_singleton, Nat.cast_ofNat] using
      abundancySup_div_abundancyIndex_le_of_single_odd_exponent 45 5
        (by decide) (by decide +kernel) (by decide +kernel) (by
          intro p hp hp5
          have : p ∈ (45 : ℕ).primeFactors.erase 5 := Finset.mem_erase.mpr ⟨hp5, hp⟩
          rw [hrest, Finset.mem_singleton] at this
          subst p
          decide +kernel)
  · unfold abundancySup abundancyIndex
    decide +kernel
