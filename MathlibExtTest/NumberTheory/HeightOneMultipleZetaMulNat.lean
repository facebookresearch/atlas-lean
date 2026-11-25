/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HeightOneMultipleZetaMulNat

open MetaMathlibExt

-- At `n = 0` the first identity is the Dirichlet series of the Riemann zeta function.
example (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => heightOneMultipleZeta s j * (0 : ℂ) ^ j) (riemannZeta s) := by
  have h := (hasSum_heightOneMultipleZeta_mul_nat_pow 0).1 s (by simpa using hs)
  simpa using h

private lemma polyBernoulliPoly_neg_one_neg (j : ℕ) :
    polyBernoulliPoly j (-((1 : ℕ) : ℤ)) (-1) = 1 := by
  have hB : ∀ i : ℕ, polyBernoulli i (-((1 : ℕ) : ℤ)) = (2 : ℚ) ^ i := by
    intro i
    rw [arakawa_kaneko_duality i 1]
    unfold polyBernoulli
    norm_num [Finset.sum_range_succ, Nat.stirlingSecond_self,
      Nat.stirlingSecond_succ_zero, zpow_neg, zpow_natCast]
  unfold polyBernoulliPoly
  have h := add_pow (2 : ℚ) (-1 : ℚ) j
  rw [show (2 : ℚ) + -1 = 1 by norm_num, one_pow] at h
  have h2 : ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℚ) * polyBernoulli i (-((1 : ℕ) : ℤ)) * (-1 : ℚ) ^ (j - i) =
      ∑ m ∈ Finset.range (j + 1),
        (2 : ℚ) ^ m * (-1 : ℚ) ^ (j - m) * (j.choose m : ℚ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hB i]
    ring
  rw [h2]
  exact h.symm

-- At `n = 1` every poly-Bernoulli coefficient in the second identity is one.
example (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => heightOneMultipleZeta (s + 1) j) (riemannZeta s) := by
  have hcast : ∀ j : ℕ,
      ((polyBernoulliPoly j (-(1 : ℤ)) (-1) : ℚ) : ℂ) = 1 := by
    intro j
    have h1 := polyBernoulliPoly_neg_one_neg j
    rw [show (-((1 : ℕ) : ℤ)) = (-(1 : ℤ)) by simp] at h1
    exact_mod_cast h1
  have h := (hasSum_heightOneMultipleZeta_mul_nat_pow 1).2 s hs
  simpa [hcast] using h

-- The first identity applied at `n = 2` and `s = 4`.
example : HasSum (fun j : ℕ => heightOneMultipleZeta 4 j * (2 : ℂ) ^ j)
    (1 / (Nat.factorial 2 : ℂ) *
      ∑ m ∈ Finset.range 3, (Nat.stirlingFirst 2 m : ℂ) * riemannZeta (4 - m)) :=
  (hasSum_heightOneMultipleZeta_mul_nat_pow 2).1 4 (by norm_num)
