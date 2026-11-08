/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.Horner
import Mathlib.Data.Fin.VecNotation
public meta import CSLibExt.Algorithms.Lean.Numerical.Horner
public meta import Mathlib.Data.Fin.VecNotation

open Cslib.Algorithms.Lean.TimeM

#eval let r := hornerEval (2 : Int) (![1, -2, 0, 3]); (r.ret, r.time)
#eval let r := hornerEval (-2 : Int) (![-1, 2, -3, 4]); (r.ret, r.time)
#eval let r := hornerEval (0 : Int) (![5, 2, -7]); (r.ret, r.time)
#eval let r := hornerEval (2 : Int) (![2, -3, 1]); (r.ret, r.time)
#eval let r := hornerEval (3 : Int) (![5, 2, 0, 0]); (r.ret, r.time)
#eval let r := hornerEval (9 : Int) (fun i : Fin 0 => Fin.elim0 i); (r.ret, r.time)
#eval let r := hornerEval (9 : Int) (![7]); (r.ret, r.time)

example : (hornerEval (2 : Int) (![1, -2, 0, 3])).ret = 21 := by decide
example : (hornerEval (-2 : Int) (![-1, 2, -3, 4])).ret = -49 := by decide
example : (hornerEval (0 : Int) (![5, 2, -7])).ret = 5 := by decide
example : (hornerEval (2 : Int) (![2, -3, 1])).ret = 0 := by decide
example : (hornerEval (3 : Int) (![5, 2, 0, 0])).ret = 11 := by decide

example (R : Type 1) [CommSemiring R] (x : R) (coefficients : Fin 3 → R) :
    (hornerEval x coefficients).time = 6 := by simp

example (R : Type 1) [CommSemiring R] [DecidableEq R] (x : R)
    (coefficients : Fin 3 → R) :
    (hornerEval x coefficients).ret = (Polynomial.ofFn 3 coefficients).eval x :=
  hornerEval_ret_eq_eval x coefficients

#check @hornerEval
#check @hornerEval_time
#check @hornerEval_ret_eq_sum
#check @hornerEval_ret_eq_eval
#check @hornerEval_empty
#check @hornerEval_singleton
#check @hornerEval_zero

#print axioms hornerEval
#print axioms hornerEval_time
#print axioms hornerEval_ret_eq_sum
#print axioms hornerEval_ret_eq_eval
#print axioms hornerEval_empty
#print axioms hornerEval_singleton
#print axioms hornerEval_zero
