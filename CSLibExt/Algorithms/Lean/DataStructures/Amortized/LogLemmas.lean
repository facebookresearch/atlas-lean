/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Amortized_Complexity/Lemmas_log.thy` (Archive of Formal Proofs, entry `Amortized Complexity`, https://isa-afp.org/entries/Amortized_Complexity.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Logarithm lemmas

`Lemmas_log.thy` from the same AFP entry (used by the splay and
pairing-heap analyses): `ld_sum_inequality`, `ld_ld_1_less`,
`ld_le_2ld`, `ld_ld_less2`. Isabelle proves them via `powr`; here
via `Real.logb_le_logb`.

Source: the AFP entry `Amortized Complexity` (Tobias Nipkow,
2014; BSD), `thys/Amortized_Complexity/Lemmas_log.thy`
(https://isa-afp.org/entries/Amortized_Complexity.html), the
base-2 logarithm lemmas of the entry's heap analyses. The lemmas
are re-established in Lean with `Real.logb`; Isabelle-derived names
are kept for traceability.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized

/- ## Log lemmas (`Lemmas_log.thy`, same AFP entry) -/

/-- `ld_sum_inequality`: `log₂ x + log₂ y + 2 ≤ 2 log₂ (x + y)` for
`x, y > 0`. Isabelle proves it via `4xy ≤ (x + y)²` and `powr`;
here via `Real.logb_le_logb`. -/
theorem ld_sum_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 x + Real.logb 2 y + 2 ≤ 2 * Real.logb 2 (x + y) := by
  have hxy : (0 : ℝ) < 4 * x * y := by positivity
  have hsum : (0 : ℝ) < (x + y) ^ 2 := pow_pos (by linarith) 2
  have hineq : (4 : ℝ) * x * y ≤ (x + y) ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hxy hsum).mpr hineq
  have h1 : Real.logb 2 (4 * x * y) = Real.logb 2 x + Real.logb 2 y + 2 := by
    rw [show (4 : ℝ) * x * y = 4 * (x * y) by ring,
      Real.logb_mul (by norm_num) (mul_ne_zero (ne_of_gt hx) (ne_of_gt hy)),
      Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow]; simp
    linarith
  have h2 : Real.logb 2 ((x + y) ^ 2) = 2 * Real.logb 2 (x + y) := by
    rw [Real.logb_pow]; ring
  rw [h1, h2] at hlog
  exact hlog

/-- `ld_ld_1_less`: `1 + log₂ x + log₂ y < 2 log₂ (x + y)`. -/
theorem ld_ld_1_less {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1 + Real.logb 2 x + Real.logb 2 y < 2 * Real.logb 2 (x + y) := by
  have h := ld_sum_inequality hx hy
  linarith

/-- `ld_le_2ld`: `log₂ (1 + x + y) ≤ 1 + log₂ (1 + x) + log₂ (1 + y)`
for `x, y ≥ 0`. -/
theorem ld_le_2ld {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.logb 2 (1 + x + y) ≤ 1 + Real.logb 2 (1 + x) + Real.logb 2 (1 + y) := by
  have h1 : (1 : ℝ) + x + y ≤ (1 + x) * (1 + y) := by
    nlinarith [mul_nonneg hx hy]
  have hpos1 : (0 : ℝ) < 1 + x + y := by linarith
  have hpos2 : (0 : ℝ) < (1 + x) * (1 + y) :=
    mul_pos (by linarith) (by linarith)
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hpos1 hpos2).mpr h1
  have hmul : Real.logb 2 ((1 + x) * (1 + y)) =
      Real.logb 2 (1 + x) + Real.logb 2 (1 + y) :=
    Real.logb_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  rw [hmul] at hlog
  linarith

/-- `ld_ld_less2`: `1 + log₂ x + log₂ y ≤ 2 log₂ (x + y - 1)` for
`x, y ≥ 2`. -/
theorem ld_ld_less2 {x y : ℝ} (hx : 2 ≤ x) (hy : 2 ≤ y) :
    1 + Real.logb 2 x + Real.logb 2 y ≤ 2 * Real.logb 2 (x + y - 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hsum : (0 : ℝ) < x + y - 1 := by linarith
  have hineq : (2 : ℝ) * x * y ≤ (x + y - 1) ^ 2 := by
    have h1 : (2 : ℝ) * x ≤ x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ x)]
    have h2 : (2 : ℝ) * y ≤ y ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 2) (by linarith : (0 : ℝ) ≤ y)]
    have key : (x + y - 1) ^ 2 - 2 * x * y =
        (x ^ 2 - 2 * x) + (y ^ 2 - 2 * y) + 1 := by ring
    linarith
  have hlog := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 2 * x * y) (pow_pos hsum 2)).mpr hineq
  have h1 : Real.logb 2 (2 * x * y) = 1 + Real.logb 2 x + Real.logb 2 y := by
    rw [show (2 : ℝ) * x * y = 2 * (x * y) by ring,
      Real.logb_mul (by norm_num) (mul_ne_zero (ne_of_gt hx0) (ne_of_gt hy0)),
      Real.logb_mul (ne_of_gt hx0) (ne_of_gt hy0),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    ring
  have h2 : Real.logb 2 ((x + y - 1) ^ 2) = 2 * Real.logb 2 (x + y - 1) := by
    rw [Real.logb_pow]; ring
  rw [h1, h2] at hlog
  exact hlog


end Amortized

end Cslib.Algorithms.Lean
