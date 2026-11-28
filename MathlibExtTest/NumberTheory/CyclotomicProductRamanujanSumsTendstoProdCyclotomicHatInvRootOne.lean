/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicProductRamanujanSumsTendstoProdCyclotomicHatInvRootOne
import Mathlib.Tactic.NormNum

/-! # Tests for constancy of an infinite cyclotomic product

The product tends to one at nonzero real and imaginary points in the open unit disk.
The first partial product at one half equals two.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 1 (`integers-2025-A96-thm-1`).
-/

open Filter Topology

namespace MathlibExtTest.NumberTheory
namespace CyclotomicProductRamanujanSumsTendstoProdCyclotomicHatInvRootOne

@[expose] public section

example :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ,
          Complex.log (1 - (1 / 2 : ℂ) * ζ))) atTop (𝓝 1) := by
  apply MetaMathlibExt.tendsto_prod_cyclotomicHat_inv_root_one
  norm_num [norm_div]

example :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ,
          Complex.log (1 - (Complex.I / 2) * ζ))) atTop (𝓝 1) := by
  apply MetaMathlibExt.tendsto_prod_cyclotomicHat_inv_root_one
  norm_num [norm_div]

example :
    (∏ n ∈ Finset.Icc (1 : ℕ) 1,
      Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ,
        Complex.log (1 - (1 / 2 : ℂ) * ζ))) = 2 := by
  norm_num [IsPrimitiveRoot.primitiveRoots_one]
  rw [Complex.exp_neg, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  norm_num

end

end CyclotomicProductRamanujanSumsTendstoProdCyclotomicHatInvRootOne
end MathlibExtTest.NumberTheory
