/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.NumberTheory.BrocardRamanujanFewPrimeFactors
public import MathlibExt.NumberTheory.BrocardRamanujanPolynomialShape
public import MathlibExt.NumberTheory.BrocardRamanujanPowerFree
public import MathlibExt.NumberTheory.FactorialDivisor
public import MathlibExt.NumberTheory.FactorialDivisorBound
public import MathlibExt.NumberTheory.PowerFree
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Defs

/-!
# The Brocard-Ramanujan equation with `k`-free integers and prime powers

Statements from Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with
7-Free Integers and Prime Powers*, INTEGERS 25 (2025), Article A71.

The condition "`x ± 1` is `k`-free" (respectively "has fewer than `l` prime
divisors", "is a prime power") is read as "`x - 1` or `x + 1` is". The paper's own
specialisation forces this reading: `(4, 5)` is listed as a solution with
`x ± 1` a prime power, while `x - 1 = 4 = 2 ^ 2` is a prime power and
`x + 1 = 6` is not. Prime divisors are counted without multiplicity, matching the
specialisation `l = 2` to prime powers.

In the Theorem 1 statements solutions are taken with `x` a natural number. Negative `x`
mirror positive ones: `x ↦ -x` swaps `|x - 1|` and `|x + 1|`, so the disjunctive conditions
are unchanged. Theorem 2 keeps `x` an integer, as the paper states it ("finitely many integer
solutions"): for a fixed polynomial `P`, negating `x` does not preserve
`x = x_1 ⋯ x_m P(x_1, …, x_m) ± 1`.
-/

open Nat

namespace MetaMathlibExt

@[expose] public section

/-- **Brocard–Ramanujan solutions with $x - 1$ or $x + 1$ seven-free.** If natural numbers $n$
and $x$ satisfy $n! + 1 = x^2$ and $x - 1$ or $x + 1$ is $7$-free, then $(n, x)$ is one of
$(4, 5)$, $(5, 11)$ and $(7, 71)$.

Source: Abderrahim Makki Naciri, *On the Brocard-Ramanujan Equation with 7-Free
Integers and Prime Powers*, INTEGERS 25 (2025), Article A71, Theorem 1(i),
second sentence (`integers-2025-A71-thm-1`). -/
public theorem_wanted brocardRamanujan_sevenFree_subset :
    {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
      ((p.2 - 1).IsPowerFree 7 ∨ (p.2 + 1).IsPowerFree 7)} ⊆
      {(4, 5), (5, 11), (7, 71)}

end

end MetaMathlibExt
