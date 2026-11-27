/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiConjugate

/-!
# Tests for conjugate golden ratio sums of base phi expansions
-/

open scoped goldenRatio

namespace MathlibExtTest.NumberTheory.Digits.BasePhiConjugate

open MetaMathlibExt MetaMathlibExt.BasePhiConjugate

-- `φ⁻¹` and `ψ⁻¹` share their integer coordinates.
example : ∃ a b : ℤ, φ ^ (-1 : ℤ) = a + b * φ ∧ ψ ^ (-1 : ℤ) = a + b * ψ :=
  pow_repr (-1)

-- The Bergman expansion `{1, -2}` of `2` has conjugate sum `ψ + ψ⁻² = 2`.
example : ∑ i ∈ ({1, -2} : Finset ℤ), ψ ^ i = ((2 : ℕ) : ℝ) :=
  conj_sum_eq (by rw [basePhiValue_one_neg_two]; norm_num)

-- For `{1, -2}`, with least element `-2`, the normalized conjugate sum `ψ³ + 1` exceeds `-ψ`.
example : -ψ < ∑ i ∈ ({1, -2} : Finset ℤ), ψ ^ (i - -2) :=
  conj_factor_gt isBergmanExpansion_one_neg_two (by decide) (by decide)

-- An even power: `ψ² = φ⁻²`.
example : ψ ^ (2 : ℤ) = φ ^ (-(2 : ℤ)) :=
  even_pow_eq ⟨1, rfl⟩

end MathlibExtTest.NumberTheory.Digits.BasePhiConjugate
