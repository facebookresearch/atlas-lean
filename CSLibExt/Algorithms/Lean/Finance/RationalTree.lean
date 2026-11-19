/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.BinomialOptimalStopping
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Exact rational finite-tree evaluator

The rational backward evaluator `snellRat` on a finite binomial tree, with
rational up probability and gross return, decodes by casting to real numbers
to the native real-valued Snell envelope
(`MathlibExt.Economics.Finance.BinomialOptimalStopping.snell` with discount
`1 / R`): `snellRat_cast_eq_snell`. Exercise is allowed at every pre-terminal
date and is forced at the horizon; there is no exercise-mask input.
-/

namespace Cslib.Algorithms.Lean.Finance.RationalTree

/-- Exact rational backward evaluator on a finite binomial tree: with no
period left the value is the exercise payoff; otherwise it is the larger of
exercising now and the discounted rational continuation, where the gross
return R divides the one-step expected value. -/
def snellRat (q R : Rat) (g : List Bool -> Rat) : Nat -> List Bool -> Rat
  | 0, s => g s
  | k + 1, s => max (g s)
      ((q * snellRat q R g k (true :: s)
        + (1 - q) * snellRat q R g k (false :: s)) / R)

theorem snellRat_cast_eq_snell (q R : Rat) (hq0 : 0 <= q) (hq1 : q <= 1)
    (hR : 0 < R) (g : List Bool -> Rat) (k : Nat) (s : List Bool) :
    ((snellRat q R g k s : Rat) : Real)
      = MathlibExt.Economics.Finance.BinomialOptimalStopping.snell
          (q : Real) (1 / (R : Real)) (fun t => ((g t : Rat) : Real)) k s := by
  have _ := hq0
  have _ := hq1
  have _ := hR
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [snellRat, MathlibExt.Economics.Finance.BinomialOptimalStopping.snell]
      rw [Rat.cast_max]
      congr 1
      push_cast
      simp only [ih]
      rw [div_eq_mul_one_div, mul_comm]
      simp only [MathlibExt.Economics.Finance.BinomialOptimalStopping.continuation]

end Cslib.Algorithms.Lean.Finance.RationalTree
