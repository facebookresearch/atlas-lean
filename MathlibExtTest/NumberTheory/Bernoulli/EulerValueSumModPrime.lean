/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.EulerValueSumModPrime
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

-- At the smallest odd prime the sum includes E₃(0) and is exactly 3/4.
private lemma sum_at_three : ∑ j ∈ range (3 + 1), (eulerPoly j).eval 0 = 3 / 4 := by
  have h (n : ℕ) : (eulerPoly n).eval 0 =
      (2 / (n + 1 : ℚ)) * (1 - 2 ^ (n + 1)) * bernoulli (n + 1) := by
    simp only [eulerPoly, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero,
      Polynomial.bernoulli_eval_zero]
    ring
  norm_num [sum_range_succ, h, bernoulli, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four]

example : ¬3 ∣ (3 / 4 : ℚ).den ∧ ratResidue 3 (3 / 4) = 0 := by
  have h := sum_euler_eval_zero_mod_prime 3 (by decide) (by decide)
  rw [sum_at_three] at h
  refine ⟨h.1, h.2.trans ?_⟩
  norm_num [ratResidue]
  exact Or.inl (by simpa only [Nat.cast_ofNat] using (ZMod.natCast_self 3))

-- At the next prime the residue is nonzero.
example : ¬5 ∣ (∑ j ∈ range (5 + 1), (eulerPoly j).eval 0).den ∧
    ratResidue 5 (∑ j ∈ range (5 + 1), (eulerPoly j).eval 0) = 4 := by
  have h := sum_euler_eval_zero_mod_prime 5 (by decide) (by decide)
  refine ⟨h.1, h.2.trans ?_⟩
  have hinv : (2 : ZMod 5)⁻¹ = 3 := by
    apply ZMod.inv_eq_of_mul_eq_one
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff' (2 * 3) 1 5).2 (by decide)
  norm_num [ratResidue, hinv]
  simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_natCast_iff' 9 4 5).2 (by decide)
