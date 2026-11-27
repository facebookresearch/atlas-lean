/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GeometricDifferentialOperators
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

/-!
# Tests for the order filtration of differential operators

Multiplication operators have order zero. On polynomials, the derivative has
order at most one but not zero: its commutator with `a` is multiplication by
the derivative of `a`.
-/

open Polynomial
open MathlibExt.RingTheory.GeometricDifferentialOperators

namespace MathlibExtTest.RingTheory.GeometricDifferentialOperators

example (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (a : A) :
    OrderLE k A 0 (Algebra.lsmul k k A a) :=
  multiplication_orderZero k A a

/-- The commutator of the derivative with `a` is multiplication by `a'`. -/
example (k : Type) [CommRing k] (a x : k[X]) :
    commutator k k[X] (derivative (R := k)) a x = derivative a * x := by
  rw [commutator_apply]
  simp [derivative_mul]

/-- The derivative has order at most one. -/
example (k : Type) [CommRing k] : OrderLE k k[X] 1 (derivative (R := k)) := by
  intro a b x
  rw [commutator_apply, commutator_apply]
  simp only [derivative_mul]
  ring

/-- The derivative does not have order zero. -/
example (k : Type) [Field k] : ¬ OrderLE k k[X] 0 (derivative (R := k)) := by
  intro h
  have := h X 1
  simp at this

end MathlibExtTest.RingTheory.GeometricDifferentialOperators
