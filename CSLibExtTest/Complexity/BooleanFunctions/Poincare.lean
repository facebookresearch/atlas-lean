/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.Poincare
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for the Poincaré inequality from OSSS

Tests for `CSLibExt.Complexity.BooleanFunctions.Poincare` on `{0, 1}^Bool`:

* `fullTree` and `fullTreeUniv` compute the Boolean function they are built from and query every
  variable (by `decide` and through `eval_fullTree`, `reveal_fullTreeUniv`);
* `InsensOutside` holds for a function of one variable and fails for a function of two;
* non-vacuity of `poincare`, `poincare_cov` and `poincare_bernoulli`: for the `AND` function at
  `p = 1/2` the conclusion is the explicit inequality `3/16 ≤ 1/2 + 1/2`, and for a constant
  function both sides are `0`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.OSSS.Poincare

/-- The `AND` of the two coordinates of `{0, 1}^Bool`. -/
def andFun (ω : ConfigSpace Bool) : Bool := ω true && ω false

/-! ## The full decision tree -/

example : fullTree andFun [true, false] =
    .node true (.node false (.leaf true) (.leaf false))
      (.node false (.leaf false) (.leaf false)) := by
  simp [fullTree, andFun, setOpen, setClosed]

example : (fullTree andFun [true, false]).eval (fun _ => true) = true := by decide
example : (fullTree andFun [true, false]).eval (fun x => x) = false := by decide
example : (fullTree andFun [true, false]).queried (fun x => x) = {true, false} := by decide

/-- `andFun` depends only on the coordinates `true` and `false`. -/
lemma andFun_insensOutside : InsensOutside andFun [true, false] := by
  intro ω ω' h
  simp [andFun, h true (by simp), h false (by simp)]

/-- `andFun` depends on the coordinate `false`, so it is not insensitive outside `[true]`. -/
example : ¬ InsensOutside andFun [true] := by
  intro h
  have := h (fun _ => true) (fun x => x) (by simp)
  simp [andFun] at this

example (ω : ConfigSpace Bool) : (fullTree andFun [true, false]).eval ω = andFun ω :=
  eval_fullTree andFun _ andFun_insensOutside ω

example (ω : ConfigSpace Bool) : (fullTreeUniv andFun).eval ω = andFun ω :=
  eval_fullTreeUniv andFun ω

example (e : Bool) : reveal νHalf (fullTreeUniv andFun) e = 1 :=
  reveal_fullTreeUniv νHalf_isProbWeight andFun e

/-! ## Non-vacuity of the Poincaré inequality -/

lemma var_andFun : var νHalf (fun ω => if andFun ω then (1 : ℝ) else 0) = 3 / 16 := by
  simp [var, cov, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  norm_num

lemma infl_andFun (e : Bool) : infl νHalf (fun ω => if andFun ω then (1 : ℝ) else 0) e = 1 / 2 := by
  cases e <;>
  · simp [infl, expect, weight, sum_configSpace_bool, andFun, bernoulliWeight, setOpen,
      setClosed]
    norm_num

/-- `poincare` for `AND` at `p = 1/2`: `Var = 3/16` and the total influence is `1`. -/
example : (3 / 16 : ℝ) ≤ 1 := by
  have h := poincare νHalf_isProbWeight andFun
  rw [var_andFun, Fintype.sum_bool, infl_andFun, infl_andFun] at h
  linarith

/-- `poincare_bernoulli` holds for every `p ∈ [0, 1]`. -/
example (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    var (bernoulliWeight p) (fun ω => if andFun ω then (1 : ℝ) else 0)
      ≤ ∑ e, infl (bernoulliWeight p) (fun ω => if andFun ω then (1 : ℝ) else 0) e :=
  poincare_bernoulli hp0 hp1 andFun

/-- For a constant function both sides of `poincare` vanish. -/
example : var νHalf (fun _ : ConfigSpace Bool => (1 : ℝ)) = 0 ∧
    ∑ e, infl νHalf (fun _ : ConfigSpace Bool => (1 : ℝ)) e = 0 := by
  constructor
  · simp [var, cov, expect, weight, sum_configSpace_bool, bernoulliWeight]; norm_num
  · simp [infl, expect]

/-- `poincare_cov` for `AND` and the linear function `gLin`. -/
example : cov νHalf (fun ω => if andFun ω then (1 : ℝ) else 0) gLin ≤ ∑ e, infl νHalf gLin e :=
  poincare_cov νHalf_isProbWeight andFun gLin

end StatMechTest.BooleanFunctions
