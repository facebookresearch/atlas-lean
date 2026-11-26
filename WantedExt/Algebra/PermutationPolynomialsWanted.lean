/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutation polynomials of the form `∑ n ∈ [1,k], h n * X ^ n`

Statements from Zhiguo Ding and Michael E. Zieve, "Permutation
Polynomials of the Form `∑_{n=1}^k h(n) X^n`", *INTEGERS* 24
(2024), Article A90 (<https://math.colgate.edu/~integers/y90/y90.pdf>).

The finite field `F_q` in Theorem 2 is represented by an arbitrary
finite field `K` of characteristic `p` and cardinality `p ^ ℓ`.
The action of the displayed polynomial is written directly as its
evaluated finite sum.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Algebra.ZModPermutationPolynomial
public import MathlibExt.Algebra.ZModPowerSum
public import MathlibExt.FieldTheory.Finite.PolynomialSumIdentity
