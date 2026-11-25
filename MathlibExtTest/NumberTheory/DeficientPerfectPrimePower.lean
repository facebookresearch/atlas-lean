/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DeficientPerfectPrimePower

open MathlibExt.NumberTheory.FkPerfectWanted

-- The exceptional prime power actually occurs, with deficient divisor one.
example : IsKLDeficientPerfect 2 1 (2 ^ 1) := by
  refine ⟨1, ?_⟩
  unfold KLDeficientPerfectWith
  decide

example (l : ℕ) : ¬ IsKLDeficientPerfect 2 l (3 ^ 2) := by
  intro h
  have h' := isKLDeficientPerfect_prime_pow_imp 3 2 2 l (by decide) (by decide) h
  exact (by decide : (3 : ℕ) ≠ 2) h'.1

example (l : ℕ) : ¬ IsKLDeficientPerfect 2 l (2 ^ 2) := by
  intro h
  have h' := isKLDeficientPerfect_prime_pow_imp 2 2 2 l (by decide) (by decide) h
  exact (by decide : (2 : ℕ) ≠ 1) h'.2

-- Exponent zero is excluded even at `l = 0`.
example : ¬ IsKLDeficientPerfect 2 0 (2 ^ 0) := by
  intro h
  have h' := isKLDeficientPerfect_prime_pow_imp 2 0 2 0 (by decide) (by decide) h
  exact (by decide : (0 : ℕ) ≠ 1) h'.2
