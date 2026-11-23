/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect powers in the Fibonacci sequence

UnsolvedMath seed problem NT-008: besides `1`, `8` and `144`, are there any other perfect powers
(numbers `a ^ b` with `a, b > 1`) in the Fibonacci sequence?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.FibonacciPerfectPowersUnsolvedMathNT008Wanted

/-!
Source: UnsolvedMath seed problem NT-008 (Are there infinitely many perfect powers in the Fibonacci
sequence?); the classical question whether 0, 1, 8 and 144 are the only perfect powers among the
Fibonacci numbers, as recalled in Y. Bugeaud, M. Mignotte and S. Siksek, Ann. of Math. 163 (2006),
abstract and Section 1. UnsolvedMath record UM-00000027 (`NT-008`), dataset ulamai/UnsolvedMath
v1.8.0.

A perfect power is `a ^ b` with `a > 1` and `b > 1`, the record's definition; `0 = F₀` and `1 = F₁ =
F₂` are not of this form, so the record's list `1, 8, 144` becomes `8 = F₆ = 2 ^ 3` and `144 = F₁₂ =
12 ^ 2`. `Nat.fib` is Mathlib's Fibonacci sequence with `F₀ = 0` and `F₁ = 1`. The title asks
whether there are infinitely many; the statement asks whether there are others besides the known
ones; the target answers both.
-/

/-- The record's question, with the answer "no": the only Fibonacci numbers of the form `a ^ b`
with `a > 1` and `b > 1` are `F₆ = 8 = 2 ^ 3` and `F₁₂ = 144 = 12 ^ 2`. -/
def fibonacciPerfectPowers : Prop :=
  ∀ n a b : ℕ, 1 < a → 1 < b → Nat.fib n = a ^ b → Nat.fib n = 8 ∨ Nat.fib n = 144

/--
Resolved true: Bugeaud, Mignotte and Siksek proved that the only perfect powers in the Fibonacci
sequence are `0, 1, 8, 144`, so the only Fibonacci numbers `a ^ b` with `a, b > 1` are `8` and
`144`; in particular there are no others and only finitely many. Source: UnsolvedMath seed problem
NT-008 (Are there infinitely many perfect powers in the Fibonacci sequence?); the classical question
whether 0, 1, 8 and 144 are the only perfect powers among the Fibonacci numbers, as recalled in Y.
Bugeaud, M. Mignotte and S. Siksek, Ann. of Math. 163 (2006), abstract and Section 1; resolution: Y.
Bugeaud, M. Mignotte and S. Siksek, Classical and modular approaches to exponential Diophantine
equations I. Fibonacci and Lucas perfect powers, Ann. of Math. (2) 163 (2006), 969-1018,
doi:10.4007/annals.2006.163.969; arXiv:math/0403046, abstract and Theorem 1: the only perfect powers
in the Fibonacci sequence are 0, 1, 8 and 144 (if F_n = y^p with p ≥ 2 then n = 0, 1, 2, 6 or 12),
https://annals.math.princeton.edu/2006/163-3/p05.
-/
public theorem_wanted fibonacciPerfectPowers_holds : fibonacciPerfectPowers

end MathlibExt.NumberTheory.FibonacciPerfectPowersUnsolvedMathNT008Wanted
