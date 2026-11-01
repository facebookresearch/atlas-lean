/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality
public import CSLibExtTest.Complexity.BooleanFunctions.Poincare

/-!
# Tests for the KKL inequality interface

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality`:

* `totalInfl` and `maxInfl` of the `AND` function on `{0, 1}^Bool` at `p = 1/2` are `1` and `1/2`;
  `kkl_var_le_quarter` and `kkl_maxInfl_ge_avg` at that function;
* `KKLHypercontractive p 0` holds (`kkl_hypercontractive_zero`), but the predicate is not a
  tautology: `KKLHypercontractive (1/2) 8` is false, refuted by the `AND` function, since
  `8 · 3/16 · log 2 > 1`;
* `kkl_inequality_total` and `kkl_inequality_max` instantiated with the trivial constant.

The instantiation with the proved constant `2` at `p = 1/2` is in the test file for
`KKL.FSRhoOptimise`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- The indicator of `andFun` as a real function. -/
noncomputable abbrev andInd : ConfigSpace Bool → ℝ := fun ω => if andFun ω then (1 : ℝ) else 0

lemma totalInfl_andInd : totalInfl νHalf andInd = 1 := by
  rw [totalInfl, Fintype.sum_bool, infl_andFun, infl_andFun]; norm_num

lemma maxInfl_andInd : maxInfl νHalf andInd = 1 / 2 := by
  unfold maxInfl
  rw [show infl νHalf andInd = fun _ => 1 / 2 from funext infl_andFun]
  exact Finset.sup'_const _ _

example : var νHalf andInd ≤ 1 / 4 := kkl_var_le_quarter νHalf andFun

example : var νHalf andInd
    = expect νHalf andInd * (1 - expect νHalf andInd) := kkl_var_indicator_eq νHalf andFun

/-- `kkl_maxInfl_ge_avg` at `AND`: `1 ≤ 2 · 1/2`. -/
example : totalInfl νHalf andInd ≤ (Fintype.card Bool : ℝ) * maxInfl νHalf andInd :=
  kkl_maxInfl_ge_avg νHalf andInd

/-! ## The predicate `KKLHypercontractive` -/

example : KKLHypercontractive (1 / 3) 0 := kkl_hypercontractive_zero _ (by norm_num) (by norm_num)

/-- The KKL conclusion at `AND` and `p = 1/2` reads `c · 3/16 · log 2 ≤ 1`. -/
lemma kkl_at_andFun {c : ℝ} (H : KKLHypercontractive (1 / 2) c) :
    c * (3 / 16) * Real.log 2 ≤ 1 := by
  have h := kkl_inequality_total H andFun
  rw [var_andFun, maxInfl_andInd, totalInfl_andInd] at h
  simpa using h

/-- `KKLHypercontractive (1/2) 8` is false: the predicate has content. -/
example : ¬ KKLHypercontractive (1 / 2) 8 := by
  intro H
  have h := kkl_at_andFun H
  have := Real.log_two_gt_d9
  linarith

/-- `kkl_inequality_max` with the trivial constant. -/
example : (0 : ℝ) * var νHalf andInd * Real.log (1 / maxInfl νHalf andInd)
    ≤ (Fintype.card Bool : ℝ) * maxInfl νHalf andInd :=
  kkl_inequality_max (kkl_hypercontractive_zero _ (by norm_num) (by norm_num)) andFun

end StatMechTest.BooleanFunctions
