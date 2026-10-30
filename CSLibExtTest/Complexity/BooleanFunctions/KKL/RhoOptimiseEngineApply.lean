/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.RhoOptimiseEngineApply
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# Tests for the rho-optimisation engine at exponent `2`

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.RhoOptimiseEngineApply`:

* `roe_card_filter_eq_erase` on `Finset Bool`;
* the headline `roe_rhoOptimise_apply : bph_RhoOptimise 2`, pushed through `bph_KKL` to
  `KKLHypercontractive (1/2) 2` and evaluated at the `AND` function on `{0, 1}^Bool`:
  `2 · 3/16 · log 2 ≤ 1`;
* `bph_RhoOptimise` is not a tautology: `bph_RhoOptimise 8` is false, because `bph_KKL` would turn
  it into `KKLHypercontractive (1/2) 8`, which `AND` refutes (`8 · 3/16 · log 2 > 1`).
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : (Finset.univ.filter (fun S : Finset Bool => S.card ≠ 0))
    = {{true}, {false}, {true, false}} := by
  rw [roe_card_filter_eq_erase]; decide

example : KKLHypercontractive (1 / 2) 2 := bph_KKL roe_rhoOptimise_apply

/-- The headline at `AND`: `2 · 3/16 · log 2 ≤ 1`. -/
example : 2 * (3 / 16) * Real.log 2 ≤ 1 := kkl_at_andFun (bph_KKL roe_rhoOptimise_apply)

/-- `bph_RhoOptimise 8` is false: the engine's conclusion has content. -/
example : ¬ bph_RhoOptimise 8 := by
  intro H
  have h := kkl_at_andFun (bph_KKL H)
  have := Real.log_two_gt_d9
  linarith

end StatMechTest.BooleanFunctions
