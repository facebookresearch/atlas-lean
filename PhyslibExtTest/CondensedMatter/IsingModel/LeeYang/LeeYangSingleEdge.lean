/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge`

* `HasLeeYangCircle` holds for the single edge at `β = 0` and `β = 1`, and for the perfect matching
  with three edges (`finiteMatching_hasLeeYangCircle`);
* `HasLeeYangCircle` fails for the single edge at `β = -1`: the polynomial
  `e^{-1}(z² + 2e² z + 1)` has the real zero `√(e⁴ - 1) - e²` of modulus less than one. So the
  predicate is not trivially true and the ferromagnetic hypothesis `0 ≤ β` of the Lee–Yang theorem
  matters;
* `leeYangPolynomial_twoVertexEdge` evaluated at `z = 1` and `β = 0` gives `4 = 2^2`, the number of
  configurations.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge

open _root_.StatMech _root_.StatMech.LeeYang _root_.StatMech.LeeYang Polynomial

-- The Lee–Yang circle property of the single edge at infinite temperature.
example : HasLeeYangCircle twoVertexEdge 0 := hasLeeYangCircle_twoVertexEdge le_rfl

-- The Lee–Yang circle property of the single edge at `β = 1`.
example : HasLeeYangCircle twoVertexEdge 1 := hasLeeYangCircle_twoVertexEdge zero_le_one

-- The Lee–Yang circle property of three disjoint edges at `β = 2`.
example : HasLeeYangCircle (finiteMatching 3) 2 :=
  finiteMatching_hasLeeYangCircle 3 (by norm_num)

-- At `β = 0` and `z = 1` the single-edge polynomial counts the four configurations.
example : (leeYangPolynomial twoVertexEdge 0).eval 1 = 4 := by
  rw [leeYangPolynomial_twoVertexEdge]
  simp only [eval_add, eval_mul, eval_C, eval_one, eval_pow, eval_X, neg_zero, Real.exp_zero]
  norm_num

-- The circle property fails in the antiferromagnetic regime `β = -1`.
example : ¬ HasLeeYangCircle twoVertexEdge (-1) := by
  intro h
  set c : ℝ := Real.exp 2 with hc
  have hc1 : 1 < c := Real.one_lt_exp_iff.mpr (by norm_num)
  set s : ℝ := Real.sqrt (c ^ 2 - 1) with hs_def
  have hs : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsc : s < c := by nlinarith
  have hexp : Real.exp (-2 * -1) = c := by rw [hc]; norm_num
  have hreal : (s - c) ^ 2 + 2 * c * (s - c) + 1 = 0 := by nlinarith
  have hroot : (leeYangComplexPolynomial twoVertexEdge (-1)).eval ((s - c : ℝ) : ℂ) = 0 := by
    rw [leeYangComplexPolynomial_twoVertexEdge_normalized]
    simp only [eval_mul, eval_C, eval_add, eval_pow, eval_X, eval_one, hexp]
    have hq : ((s - c : ℝ) : ℂ) ^ 2 + (2 * c : ℂ) * ((s - c : ℝ) : ℂ) + 1 = 0 := by
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hreal
    rw [hq, mul_zero]
  have hnorm := h _ hroot
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)] at hnorm
  nlinarith

end PhyslibExtTest.CondensedMatter.IsingModel.LeeYang.LeeYangSingleEdge
