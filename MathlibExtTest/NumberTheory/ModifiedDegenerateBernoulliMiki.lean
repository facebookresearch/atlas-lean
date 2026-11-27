/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliMiki

open Finset

namespace MetaMathlibExt.modifiedDegenerateBernoulli_miki

local notation "B" => modifiedDegenerateBernoulli

private theorem odd_at_zero (lam : ℂ) {k : ℕ} (hk : Odd k) (hk' : 1 < k) : B lam k 0 = 0 := by
  simp [modifiedDegenerateBernoulli, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
    Polynomial.coeff_bernoulli, bernoulli_eq_zero_of_odd hk hk']

-- At the first allowed degree only the middle summand and the harmonic term survive.
example (lam : ℂ) (h₀ : lam ≠ 0) (h₁ : lam ≠ -1) :
    -(5 / 2) * (B lam 2 0) ^ 2 =
      (25 / 12) * (lam / Complex.log (1 + lam)) * B lam 4 0 := by
  have h := modifiedDegenerateBernoulli_miki 4 (by decide) lam h₀ h₁
  have h₃ : B lam 3 0 = 0 := odd_at_zero lam (by decide) (by decide)
  have hI : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  norm_num [hI, Nat.choose, harmonic_succ, h₃] at h
  linear_combination h

-- At the first odd degree the harmonic term vanishes and the degree-four correction remains.
example (lam : ℂ) (h₀ : lam ≠ 0) (h₁ : lam ≠ -1) :
    (∑ k ∈ Icc 1 4, B lam k 0 / k * B lam (5 - k) 0) -
      (∑ k ∈ Icc 1 4, (Nat.choose 5 k : ℂ) * B lam k 0 / k * B lam (5 - k) 0) =
      5 / 2 * B lam 4 0 := by
  simpa only [show 5 - 1 = 4 by decide, Nat.cast_ofNat,
    odd_at_zero lam (show Odd 5 by decide) (by decide), mul_zero, zero_add] using
    modifiedDegenerateBernoulli_miki 5 (by decide) lam h₀ h₁

end MetaMathlibExt.modifiedDegenerateBernoulli_miki
