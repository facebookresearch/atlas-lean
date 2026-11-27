/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the divisibility of sums of Fibonacci numbers

Statements from Oisín Flynn-Connolly, "On the Divisibility
of Sums of Fibonacci Numbers", *INTEGERS* 25 (2025), Article A87
(<https://math.colgate.edu/~integers/z87/z87.pdf>).

The paper's Proposition 1, `S n = F (n + 2) - 1`, is already
Mathlib's `Nat.fib_succ_eq_succ_sum`, so it is not re-requested
here.  The Pisano period is the minimal period of the Fibonacci
pair step on `ZMod n × ZMod n` at `(0, 1)`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibility
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilityPrimeIndices
public import MathlibExt.NumberTheory.Recurrences.OddFibonacciSumDivisibility
public import MathlibExt.NumberTheory.Recurrences.FibonacciSumDivisibilitySumFibModPrimeEqAndNotDvd
public import MathlibExt.NumberTheory.Recurrences.PisanoPeriodMinRatio
