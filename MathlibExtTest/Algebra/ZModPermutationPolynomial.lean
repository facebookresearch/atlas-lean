/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ZModPermutationPolynomial

namespace MathlibExt.Algebra.PermutationPolynomialsWanted

-- Only the congruence modulo p² holds in the disjunction.
example : Function.Bijective
    (fun c : ZMod 3 => ∑ n ∈ Finset.Icc (1 : ℕ) 19, (n : ZMod 3) ^ 2 * c ^ n) :=
  bijective_sum_pow_mul_pow_zmod 3 19 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (by decide))

-- Only the nondivisibility of t holds in the disjunction.
example : Function.Bijective
    (fun c : ZMod 3 => ∑ n ∈ Finset.Icc (1 : ℕ) 7, (n : ZMod 3) ^ 3 * c ^ n) :=
  bijective_sum_pow_mul_pow_zmod 3 7 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inr (by decide))

-- The interval contains one term, with no full blocks of length p.
example : Function.Bijective
    (fun c : ZMod 3 => ∑ n ∈ Finset.Icc (1 : ℕ) 1, (n : ZMod 3) ^ 2 * c ^ n) :=
  bijective_sum_pow_mul_pow_zmod 3 1 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (Or.inl (by decide))

end MathlibExt.Algebra.PermutationPolynomialsWanted
